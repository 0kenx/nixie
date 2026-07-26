; Test: no integer square root of -1
; Expected: unsat
(set-logic QF_NIA)
(declare-const x Int)
(assert (= (+ (* x x) 1) 0))
(check-sat)
