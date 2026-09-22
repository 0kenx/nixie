; Reference: unsat. Nixie's finite-shape fragment deliberately returns unknown.
(set-logic ALL)
(set-info :status unsat)
(declare-const h (Seq Int))
(declare-const x Int)
(assert (distinct (seq.len (seq.++ h (seq.unit x))) (+ (seq.len h) 1)))
(check-sat)
