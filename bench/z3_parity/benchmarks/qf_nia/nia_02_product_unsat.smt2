; Test: product with contradictory bounds
; Expected: unsat
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (= (* x y) 1))
(assert (> x 1))
(assert (> y 1))
(check-sat)
