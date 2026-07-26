;; expected: sat
; x*y = 6 with 1 ≤ x,y ≤ 3
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 1) (<= x 3) (>= y 1) (<= y 3) (= (* x y) 6)))
(check-sat)
