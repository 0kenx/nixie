//! Scratch move records for one complete, callback-free watch-list scan.
use super::{Lit, Watcher};
#[allow(unused_imports)]
use crate::prelude::*;
use core::{fmt, marker::PhantomData, mem::MaybeUninit};

#[derive(Clone, Copy)]
struct DelayedWatch {
    literal: Lit,
    watcher: Watcher,
}

/// Capacity only: initialized records belong to a scoped writer, never to
/// logical watch-list state. Cloning a solver does not copy stale scratch.
#[derive(Default)]
pub(crate) struct MoveBuffer {
    slots: Vec<MaybeUninit<DelayedWatch>>,
}

impl Clone for MoveBuffer {
    fn clone(&self) -> Self {
        Self::default()
    }
}

impl fmt::Debug for MoveBuffer {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        // Like Vec's Debug, logical contents do not include allocation slack.
        // An active writer exclusively borrows us, so it cannot be observed.
        f.write_str("MoveBuffer")
    }
}

pub(crate) struct MoveWriter<'a> {
    begin: *mut DelayedWatch,
    next: *mut DelayedWatch,
    #[cfg(debug_assertions)]
    end: *mut DelayedWatch,
    owner: PhantomData<&'a mut [MaybeUninit<DelayedWatch>]>,
}

pub(crate) struct Moves<'a> {
    initialized: &'a [DelayedWatch],
}

impl MoveBuffer {
    #[inline]
    #[allow(unsafe_code)]
    pub(crate) fn prepare(&mut self, watchers: usize) -> MoveWriter<'_> {
        if self.slots.len() < watchers {
            self.slots.resize_with(watchers, MaybeUninit::uninit);
        }
        let begin = self.slots.as_mut_ptr().cast::<DelayedWatch>();
        MoveWriter {
            begin,
            next: begin,
            // SAFETY: resize established at least watchers allocation slots;
            // MaybeUninit<T> has T's layout and permits uninitialized storage.
            #[cfg(debug_assertions)]
            end: unsafe { begin.add(watchers) },
            owner: PhantomData,
        }
    }

    pub(crate) fn capacity_bytes(&self) -> usize {
        self.slots.capacity() * core::mem::size_of::<DelayedWatch>()
    }
}

impl<'a> MoveWriter<'a> {
    /// # Safety
    /// The caller must append no more records than the watcher count passed
    /// to prepare. The complete-list kernel appends at most once per visited
    /// watcher, including across its single prefix-to-suffix transition.
    #[inline]
    #[allow(unsafe_code)]
    pub(crate) unsafe fn push(&mut self, literal: Lit, watcher: Watcher) {
        #[cfg(debug_assertions)]
        debug_assert!(self.next != self.end);
        // SAFETY: the caller's visit bound guarantees this unused slot is
        // within the exclusive allocation. No reference aliases its contents.
        unsafe {
            self.next.write(DelayedWatch { literal, watcher });
            self.next = self.next.add(1);
        }
    }

    #[inline]
    #[allow(unsafe_code)]
    pub(crate) fn finish(self) -> Moves<'a> {
        // SAFETY: push initializes every slot in [begin,next) exactly once.
        // Both coordinates remain within the same allocation; equal pointers
        // handle empty buffers. Consuming the writer ends all mutable access.
        let initialized = unsafe {
            let len = self.next.offset_from(self.begin) as usize;
            core::slice::from_raw_parts(self.begin, len)
        };
        Moves { initialized }
    }
}

impl Moves<'_> {
    #[inline]
    pub(crate) fn is_empty(&self) -> bool {
        self.initialized.is_empty()
    }

    /// Publish in encounter order before another literal can be dequeued.
    #[inline(never)]
    pub(crate) fn flush(self, destinations: &mut [Vec<Watcher>]) {
        for entry in self.initialized {
            destinations[entry.literal.index()].push(entry.watcher);
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::{clause::ClauseId, memory::ClauseRef};

    #[test]
    #[allow(unsafe_code)]
    fn empty_partial_full_move_prefixes_flush_in_order_and_reuse_storage() {
        let mut buffer = MoveBuffer::default();
        for bound in [0, 1, 7, 97, 3, 0] {
            for used in 0..=bound {
                let mut lists = vec![Vec::new(); 4];
                let mut writer = buffer.prepare(bound);
                for i in 0..used {
                    let watcher = Watcher::new(
                        ClauseId::new(i as u32),
                        ClauseRef::NULL,
                        Lit::from_code((i + 10) as u32),
                    );
                    // SAFETY: used <= bound, each iteration appends once.
                    unsafe { writer.push(Lit::from_code((i % 4) as u32), watcher) };
                }
                writer.finish().flush(&mut lists);
                for (destination, list) in lists.iter().enumerate() {
                    assert_eq!(
                        list.iter().map(|w| w.blocker.index()).collect::<Vec<_>>(),
                        (0..used)
                            .filter(|i| i % 4 == destination)
                            .map(|i| i + 10)
                            .collect::<Vec<_>>()
                    );
                }
            }
        }
        assert!(buffer.capacity_bytes() >= 97 * core::mem::size_of::<DelayedWatch>());
        let mut cloned = buffer.clone();
        assert_eq!(cloned.capacity_bytes(), 0);
        cloned.prepare(0).finish().flush(&mut []);
        buffer.prepare(0).finish().flush(&mut []);
    }
}
