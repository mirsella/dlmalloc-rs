use crate::Allocator;
#[cfg(target_arch = "wasm32")]
use core::arch::wasm32 as wasm;
#[cfg(target_arch = "wasm64")]
use core::arch::wasm64 as wasm;
use core::ptr;
use core::sync::atomic::{AtomicUsize, Ordering};

extern "C" {
    static __heap_base: u8;
}

static BUMP: AtomicUsize = AtomicUsize::new(0);

fn align_up(value: usize, alignment: usize) -> Option<usize> {
    value
        .checked_add(alignment - 1)
        .map(|v| v & !(alignment - 1))
}

fn alloc_from_preexisting(
    size: usize,
    page_size: usize,
    current_memory: usize,
    bump: usize,
    heap_base: usize,
) -> Option<(usize, usize, usize)> {
    let start = if bump == 0 {
        align_up(heap_base, page_size)?
    } else {
        bump
    };

    if start == 0 {
        return None;
    }

    if start >= current_memory {
        return None;
    }

    let remaining = current_memory - start;
    if remaining < size {
        return None;
    }

    Some((start, remaining, current_memory))
}

/// System setting for Wasm
pub struct System {
    _priv: (),
}

impl System {
    pub const fn new() -> System {
        System { _priv: () }
    }
}

unsafe impl Allocator for System {
    fn alloc(&self, size: usize) -> (*mut u8, usize, u32) {
        if size == 0 {
            return (ptr::null_mut(), 0, 0);
        }

        let page_size = self.page_size();
        let current_memory = match wasm::memory_size(0).checked_mul(page_size) {
            Some(v) => v,
            None => return (ptr::null_mut(), 0, 0),
        };

        let heap_base = unsafe { &__heap_base as *const u8 as usize };
        let bump = BUMP.load(Ordering::Relaxed);
        if let Some((base, len, next_bump)) =
            alloc_from_preexisting(size, page_size, current_memory, bump, heap_base)
        {
            // Mark all pre-existing memory as consumed so we won't ever hand it
            // out again after subsequent growth.
            BUMP.store(next_bump, Ordering::Relaxed);
            return (base as *mut u8, len, 0);
        }

        let rounded = match size.max(page_size).checked_add(page_size - 1) {
            Some(v) => v & !(page_size - 1),
            None => return (ptr::null_mut(), 0, 0),
        };
        let pages = rounded / page_size;
        let prev = wasm::memory_grow(0, pages);

        // If the allocation failed, meaning `prev` is -1 or
        // `usize::max_value()`, then return null.
        if prev == usize::max_value() {
            return (ptr::null_mut(), 0, 0);
        }

        let prev_page = prev * page_size;
        let base_ptr = prev_page as *mut u8;
        let size = pages * page_size;

        // Prevent later allocations from treating the newly grown pages as
        // "pre-existing" memory.
        if let Some(new_end) = prev_page.checked_add(size) {
            BUMP.store(new_end, Ordering::Relaxed);
        }

        // Additionally check to see if we just allocated the final bit of the
        // address space. In such a situation it's not valid in Rust for a
        // pointer to actually wrap around to from the top of the address space
        // to 0, so it's not valid to allocate the entire region. Fake the last
        // few bytes as being un-allocated meaning that the actual size of this
        // allocation won't be page aligned, which should be handled by
        // dlmalloc.
        if prev_page.wrapping_add(size) == 0 {
            BUMP.store(usize::MAX, Ordering::Relaxed);
            return (base_ptr, size - 16, 0);
        }

        (base_ptr, size, 0)
    }

    fn remap(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize, _can_move: bool) -> *mut u8 {
        // TODO: I think this can be implemented near the end?
        ptr::null_mut()
    }

    fn free_part(&self, _ptr: *mut u8, _oldsize: usize, _newsize: usize) -> bool {
        false
    }

    fn free(&self, _ptr: *mut u8, _size: usize) -> bool {
        false
    }

    fn can_release_part(&self, _flags: u32) -> bool {
        false
    }

    fn allocates_zeros(&self) -> bool {
        true
    }

    fn page_size(&self) -> usize {
        64 * 1024
    }
}

#[cfg(test)]
mod tests {
    use super::{align_up, alloc_from_preexisting};

    fn legacy_grow_only(
        size: usize,
        page_size: usize,
        grow_result: usize,
    ) -> Option<(usize, usize)> {
        let pages = size.div_ceil(page_size);
        if grow_result == usize::MAX {
            return None;
        }
        Some((grow_result * page_size, pages * page_size))
    }

    #[test]
    fn uses_preexisting_memory_when_growth_fails() {
        let page_size = 64 * 1024;
        let current_memory = page_size * 4;
        let bump = page_size;
        let heap_base = 0;

        let new_behavior = alloc_from_preexisting(16, page_size, current_memory, bump, heap_base);
        let legacy_behavior = legacy_grow_only(16, page_size, usize::MAX);

        assert_eq!(
            new_behavior,
            Some((page_size, page_size * 3, current_memory))
        );
        assert_eq!(legacy_behavior, None);
    }

    #[test]
    fn aligns_heap_base_when_bump_uninitialized() {
        let page_size = 64 * 1024;
        let current_memory = page_size * 3;
        let heap_base = page_size + 17;
        let expected = align_up(heap_base, page_size).unwrap();

        let alloc = alloc_from_preexisting(1, page_size, current_memory, 0, heap_base).unwrap();
        assert_eq!(alloc.0, expected);
        assert_eq!(alloc.1, current_memory - expected);
        assert_eq!(alloc.2, current_memory);
    }

    #[test]
    fn returns_none_when_remaining_too_small() {
        let page_size = 64 * 1024;
        let current_memory = page_size * 2;
        let bump = current_memory - 8;

        let alloc = alloc_from_preexisting(16, page_size, current_memory, bump, 0);
        assert_eq!(alloc, None);
    }

    #[test]
    fn does_not_treat_grown_pages_as_preexisting() {
        let page_size = 64 * 1024;
        let preexisting_end = page_size * 4;
        let after_grow_current_memory = page_size * 6;
        let heap_base = page_size;
        let start = align_up(heap_base, page_size).unwrap();

        let alloc = alloc_from_preexisting(16, page_size, preexisting_end, 0, heap_base).unwrap();
        assert_eq!(alloc.0, start);
        assert_eq!(alloc.1, preexisting_end - start);

        // If the allocator incorrectly used `current_memory` after growth as
        // the pre-existing limit, it would hand out a region that includes the
        // grown pages, overlapping memory already returned by `memory.grow`.
        let incorrect =
            alloc_from_preexisting(16, page_size, after_grow_current_memory, 0, heap_base).unwrap();
        assert_eq!(incorrect.1, after_grow_current_memory - start);
        assert_ne!(alloc.1, incorrect.1);
    }

    #[test]
    fn bump_prevents_reusing_preexisting_after_growth() {
        let page_size = 64 * 1024;
        let current_memory = page_size * 6;

        // After a successful memory.grow, we set BUMP to the new end.
        // That must prevent the pre-existing allocator from handing out any
        // region based on the new `current_memory`.
        let bump = current_memory;
        let heap_base = 0;

        let alloc = alloc_from_preexisting(16, page_size, current_memory, bump, heap_base);
        assert_eq!(alloc, None);
    }
}

#[cfg(feature = "global")]
pub fn acquire_global_lock() {
    // single threaded, no need!
    assert!(!cfg!(target_feature = "atomics"));
}

#[cfg(feature = "global")]
pub fn release_global_lock() {
    // single threaded, no need!
    assert!(!cfg!(target_feature = "atomics"));
}

#[allow(missing_docs)]
#[cfg(feature = "global")]
pub unsafe fn enable_alloc_after_fork() {
    // single threaded, no need!
    assert!(!cfg!(target_feature = "atomics"));
}
