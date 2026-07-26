;; expected: sat
; x*y = 12 with −5 ≤ x,y ≤ 5
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x (- 5)) (<= x 5) (>= y (- 5)) (<= y 5) (= (* x y) 12)))
(check-sat)
