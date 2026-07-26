; Test: integer division with constant divisor
; Expected: sat
(set-logic QF_NIA)
(declare-const x Int)
(assert (= (div x 3) 2))
(assert (>= x 0))
(assert (<= x 20))
(check-sat)
