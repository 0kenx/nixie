;; expected: sat
; x*y*z = 24 with 1 ≤ x,y,z ≤ 10
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(declare-const z Int)
(assert (and (>= x 1) (<= x 10) (>= y 1) (<= y 10) (>= z 1) (<= z 10) (= (* x y z) 24)))
(check-sat)
