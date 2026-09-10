//! A fixed-domain propagation session. Truth bytes and assignment-only state
//! have disjoint borrows, so a watch scan need not retain queue/metadata bases.
use super::{ClauseId, LBool, Lit, Reason, Trail, VarInfo};
#[allow(unused_imports)]
use crate::prelude::*;

pub(crate) struct PropagationTrail<'a> {
    pub(crate) values: &'a mut [i8],
    pub(crate) queue: PropagationQueue<'a>,
}

pub(crate) struct PropagationQueue<'a> {
    assignments: &'a mut Vec<Lit>,
    published_head: &'a mut usize,
    queue: *mut Lit,
    initialized: usize,
    head: usize,
    info: &'a mut [VarInfo],
    level: u32,
}

impl Trail {
    pub(crate) fn propagation_session(&mut self) -> PropagationTrail<'_> {
        // General Trail APIs permit repeated entries in the old prefix. Only
        // undefined variables append in this session, at most domain size more.
        self.assignments.reserve(self.var_info.len());
        let initialized = self.assignments.len();
        let queue = self.assignments.as_mut_ptr();
        let head = self.prop_head;
        PropagationTrail {
            values: &mut self.values,
            queue: PropagationQueue {
                assignments: &mut self.assignments,
                published_head: &mut self.prop_head,
                queue,
                initialized,
                head,
                info: &mut self.var_info,
                level: self.current_level,
            },
        }
    }
}

/// The same valid solver-literal domain contract as Trail::lit_val_hot.
#[inline]
#[allow(unsafe_code)]
pub(crate) fn propagation_value(values: &[i8], lit: Lit) -> i8 {
    debug_assert!(lit.index() < values.len());
    // SAFETY: Solver grows both truth signs before constructing any watch,
    // edge or trail literal. The session excludes resizing and unassignment.
    unsafe { *values.get_unchecked(lit.index()) }
}

/// Kissat `inlineassign.h` prefetches `WATCHES(not_lit)` at assign time so
/// the later scan of that list overlaps remaining work. Locality 1 is
/// `_MM_HINT_T2`. Empty lists are skipped. This does not change solver state.
#[inline]
pub(crate) fn prefetch_watch_payload<T>(slice: &[T]) {
    if slice.is_empty() {
        return;
    }
    #[cfg(target_arch = "x86_64")]
    {
        #[allow(unsafe_code)]
        unsafe {
            core::arch::x86_64::_mm_prefetch(
                slice.as_ptr().cast::<i8>(),
                core::arch::x86_64::_MM_HINT_T2,
            );
        }
    }
}

/// Assign through the disjoint truth/queue views.
///
/// # Safety
/// These must be the two parts of the same active propagation session, and
/// lit must be in-domain and currently undefined. No variable may be unassigned
/// during the session; thus the reserved additional capacity bounds appends.
#[inline]
#[allow(unsafe_code)]
pub(crate) unsafe fn assign_undefined(
    values: &mut [i8],
    queue: &mut PropagationQueue<'_>,
    lit: Lit,
    reason: ClauseId,
) {
    let code = lit.index();
    debug_assert!(code < values.len() && (code ^ 1) < values.len());
    debug_assert_eq!(values[code], 0);
    // SAFETY: the caller's undefined-variable contract bounds total appends.
    // The leaf checks its domain/capacity before touching initialized state.
    unsafe { queue.append(lit, reason) };
    // SAFETY: both signs are in the fixed exclusive truth slice. The append
    // cannot run callbacks; these stores complete the assignment before any
    // subsequent scan/dequeue can observe it. Neither store can unwind.
    unsafe {
        *values.get_unchecked_mut(code) = 1;
        *values.get_unchecked_mut(code ^ 1) = -1;
    }
}

impl PropagationQueue<'_> {
    #[inline]
    #[allow(unsafe_code)]
    pub(crate) fn next(&mut self) -> Option<Lit> {
        if self.head >= self.initialized {
            return None;
        }
        // SAFETY: only initialized entries are read; the exclusive queue
        // borrow prevents reallocation or aliased element references.
        let lit = unsafe { self.queue.add(self.head).read() };
        self.head += 1;
        Some(lit)
    }

    #[inline]
    pub(crate) fn requeue(&mut self) {
        debug_assert!(self.head > 0);
        self.head = self.head.saturating_sub(1);
    }

    // Assignment-only state stays behind this leaf rather than competing
    // with the arena/value bases in every blocker and tail-literal visit.
    #[inline(never)]
    #[allow(unsafe_code)]
    unsafe fn append(&mut self, lit: Lit, reason: ClauseId) {
        let idx = lit.var().index();
        debug_assert!(idx < self.info.len());
        debug_assert!(self.initialized < self.assignments.capacity());
        // SAFETY: the session reserves domain-size additional capacity. Its
        // caller assigns each newly defined variable at most once, and the
        // valid literal identifies an initialized metadata slot. No element
        // reference aliases the queue's raw initialized/uninitialized prefix.
        unsafe {
            *self.info.get_unchecked_mut(idx) = VarInfo {
                value: if lit.is_pos() {
                    LBool::True
                } else {
                    LBool::False
                },
                level: self.level,
                reason: Reason::Propagation(reason),
                trail_idx: self.initialized as u32,
            };
            self.queue.add(self.initialized).write(lit);
        }
        self.initialized += 1;
    }
}

impl Drop for PropagationQueue<'_> {
    #[inline]
    #[allow(unsafe_code)]
    fn drop(&mut self) {
        // SAFETY: every slot below initialized has been initialized, and no
        // slot exceeds the reserved allocation. Lit is Copy with no destructor.
        // No further raw access occurs after publishing, including on unwind.
        unsafe { self.assignments.set_len(self.initialized) };
        *self.published_head = self.head;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    #[allow(unsafe_code)]
    fn session_queue_matches_scalar_with_duplicates_requeue_and_reborrow() {
        for n in [0, 1, 5, 65] {
            let mut trail = Trail::new(n);
            let mut scalar = Trail::new(n);
            for t in [&mut trail, &mut scalar] {
                if n != 0 {
                    for _ in 0..3 {
                        t.assign_unit_fact(Lit::from_code(0));
                    }
                    assert_eq!(t.next_to_propagate(), Some(Lit::from_code(0)));
                }
                t.new_decision_level();
            }
            for round in 0..2 {
                {
                    let mut session = trail.propagation_session();
                    if round == 0 {
                        for i in 1..n {
                            let lit = Lit::from_code((2 * i + i % 2) as u32);
                            let reason = ClauseId::new(i as u32);
                            assert_eq!(propagation_value(session.values, lit), 0);
                            // SAFETY: paired views, each valid variable once.
                            unsafe {
                                assign_undefined(session.values, &mut session.queue, lit, reason)
                            };
                            scalar.assign_propagation(lit, reason);
                            assert_eq!(propagation_value(session.values, lit), 1);
                            assert_eq!(propagation_value(session.values, !lit), -1);
                        }
                    }
                    while let Some(lit) = session.queue.next() {
                        assert_eq!(Some(lit), scalar.next_to_propagate());
                    }
                    assert_eq!(scalar.next_to_propagate(), None);
                    if n != 0 {
                        session.queue.requeue();
                        scalar.requeue_last_propagated();
                    }
                }
                assert_eq!(format!("{trail:?}"), format!("{scalar:?}"));
            }
        }
    }

    #[test]
    #[allow(unsafe_code)]
    fn session_queue_unwind_publishes_initialized_prefix_and_head() {
        let mut trail = Trail::new(3);
        let mut scalar = Trail::new(3);
        let lit = Lit::from_code(3);
        let reason = ClauseId::new(7);
        let outcome = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
            let mut session = trail.propagation_session();
            // SAFETY: paired views and an in-domain undefined variable.
            unsafe { assign_undefined(session.values, &mut session.queue, lit, reason) };
            assert_eq!(session.queue.next(), Some(lit));
            panic!("exercise session publication");
        }));
        assert!(outcome.is_err());
        scalar.assign_propagation(lit, reason);
        assert_eq!(scalar.next_to_propagate(), Some(lit));
        assert_eq!(format!("{trail:?}"), format!("{scalar:?}"));
        trail.resize(128);
        scalar.resize(128);
        trail.backtrack_to_size(0);
        scalar.backtrack_to_size(0);
        assert_eq!(format!("{trail:?}"), format!("{scalar:?}"));
    }
}
