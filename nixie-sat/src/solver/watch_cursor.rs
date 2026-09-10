//! Exclusive initialized watch-slice traversal with stable compaction.
//! All raw coordinates stay within one borrowed slice. No element references
//! escape, and a pending entry must be consumed before the next can be read.
use super::{Lit, Watcher};
use core::marker::PhantomData;

pub(super) struct WatchCursor<'a, const COMPACT: bool> {
    read: *mut Watcher,
    write: *mut Watcher,
    end: *mut Watcher,
    owner: PhantomData<&'a mut [Watcher]>,
}

pub(super) struct Entry<'c, 'a, const COMPACT: bool> {
    cursor: &'c mut WatchCursor<'a, COMPACT>,
    watcher: Watcher,
}

impl<'a> WatchCursor<'a, false> {
    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn new(watches: &'a mut [Watcher]) -> Self {
        let begin = watches.as_mut_ptr();
        Self {
            read: begin,
            write: begin,
            // SAFETY: one-past-end of this initialized slice, including empty.
            end: unsafe { begin.add(watches.len()) },
            owner: PhantomData,
        }
    }
}

impl<'a, const COMPACT: bool> WatchCursor<'a, COMPACT> {
    /// Materialize the consumed coordinates as local state. The list kernel
    /// must not retain the caller's indirect argument as its mutable cursor.
    #[inline]
    pub(super) fn into_local(self) -> Self {
        Self {
            read: self.read,
            write: self.write,
            end: self.end,
            owner: PhantomData,
        }
    }

    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn next(&mut self) -> Option<Entry<'_, 'a, COMPACT>> {
        if self.read == self.end {
            return None;
        }
        if !COMPACT {
            self.write = self.read;
        }
        // SAFETY: read advances exactly once per nonempty next, never past
        // end. Keeping writes strictly behind the newly advanced read cursor.
        // The Entry borrow excludes another next/finish until it is consumed.
        let watcher = unsafe {
            let watcher = self.read.read();
            self.read = self.read.add(1);
            watcher
        };
        Some(Entry {
            cursor: self,
            watcher,
        })
    }

    #[inline]
    pub(super) fn compacting(self) -> WatchCursor<'a, true> {
        // After a removed prefix entry, write names precisely its hole. No
        // subtraction from begin/end or unchecked nonempty assumption occurs.
        WatchCursor {
            read: self.read,
            write: self.write,
            end: self.end,
            owner: PhantomData,
        }
    }

    /// Publish the kept prefix plus the untouched remainder on early conflict.
    /// The returned pointer belongs to the original slice and is never read.
    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn finish(self) -> *mut Watcher {
        if !COMPACT {
            return self.end;
        }
        // SAFETY: read <= end and write <= read in the same allocation.
        // Both ranges are initialized and fit inside the original slice;
        // copy explicitly permits overlap. Watcher is Copy. Equal pointers
        // cover empty slices without a nonempty-allocation assumption.
        unsafe {
            let remaining = self.end.offset_from(self.read) as usize;
            core::ptr::copy(self.read, self.write, remaining);
            self.write.add(remaining)
        }
    }
}

impl<const COMPACT: bool> Entry<'_, '_, COMPACT> {
    #[inline]
    pub(super) fn watcher(&self) -> Watcher {
        self.watcher
    }

    #[inline]
    #[allow(unsafe_code)]
    pub(super) fn keep(self, blocker: Option<Lit>) {
        // SAFETY: next established write < read <= end. Consuming this token
        // permits exactly one keep, and its exclusive borrow prevents another
        // next from changing coordinates. No element reference aliases writes.
        unsafe {
            if COMPACT {
                let mut watcher = self.watcher;
                if let Some(blocker) = blocker {
                    watcher.blocker = blocker;
                }
                self.cursor.write.write(watcher);
                self.cursor.write = self.cursor.write.add(1);
            } else if let Some(blocker) = blocker {
                (*self.cursor.write).blocker = blocker;
            }
        }
    }

    #[inline]
    pub(super) fn remove(self) {}
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::clause::ClauseId;
    use crate::memory::ClauseRef;
    #[allow(unused_imports)]
    use crate::prelude::*;

    #[test]
    #[allow(unsafe_code)]
    fn cursor_keeps_removes_and_copies_every_unvisited_suffix() {
        for len in 0..=7 {
            for mask in 0..1usize << len {
                for stop in 0..=len {
                    let mut watches: Vec<_> = (0..len)
                        .map(|i| {
                            Watcher::new(
                                ClauseId::new(i as u32),
                                ClauseRef::NULL,
                                Lit::from_code(i as u32),
                            )
                        })
                        .collect();
                    let begin = watches.as_mut_ptr();
                    let mut cursor = WatchCursor::new(&mut watches).compacting();
                    let mut expected = Vec::new();
                    for i in 0..stop {
                        let Some(entry) = cursor.next() else {
                            panic!("initialized slot missing")
                        };
                        assert_eq!(entry.watcher().blocker.index(), i);
                        if mask & (1 << i) != 0 {
                            entry.keep(Some(Lit::from_code((i + 20) as u32)));
                            expected.push(i + 20);
                        } else {
                            entry.remove();
                        }
                    }
                    expected.extend(stop..len);
                    let end = cursor.finish();
                    // SAFETY: endpoint from the same exclusive slice cursor.
                    let kept = unsafe { end.offset_from(begin) as usize };
                    assert_eq!(
                        watches[..kept]
                            .iter()
                            .map(|w| w.blocker.index())
                            .collect::<Vec<_>>(),
                        expected
                    );
                }
            }
        }
    }

    #[test]
    #[allow(unsafe_code)]
    fn cursor_prefix_first_last_holes_and_empty_transitions() {
        for len in 0..=7 {
            for hole in 0..=len {
                let mut watches: Vec<_> = (0..len)
                    .map(|i| {
                        Watcher::new(
                            ClauseId::new(i as u32),
                            ClauseRef::NULL,
                            Lit::from_code(i as u32),
                        )
                    })
                    .collect();
                let begin = watches.as_mut_ptr();
                let mut prefix = WatchCursor::new(&mut watches);
                for _ in 0..hole {
                    let Some(entry) = prefix.next() else {
                        panic!("prefix missing")
                    };
                    entry.keep(None);
                }
                let end = if let Some(entry) = prefix.next() {
                    entry.remove();
                    prefix.compacting().finish()
                } else {
                    prefix.finish()
                };
                // SAFETY: endpoint from the same exclusive slice cursor.
                let kept = unsafe { end.offset_from(begin) as usize };
                let expected: Vec<_> = (0..len).filter(|&i| i != hole).collect();
                assert_eq!(
                    watches[..kept]
                        .iter()
                        .map(|w| w.blocker.index())
                        .collect::<Vec<_>>(),
                    expected
                );
            }
        }
    }
}
