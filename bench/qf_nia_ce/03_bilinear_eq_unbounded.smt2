;; expected: sat
; x*y = 12 with x,y ≥ 1 (no upper bound)
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 1) (>= y 1) (= (* x y) 12)))
(check-sat)
