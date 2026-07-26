; Test: product zero with both positive
; Expected: unsat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 0))
(assert (> x 0))
(assert (> y 0))
(check-sat)
