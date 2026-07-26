;; expected: sat
; x*y = 12 with 1 ≤ x,y ≤ 10
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 1) (<= x 10) (>= y 1) (<= y 10) (= (* x y) 12)))
(check-sat)
