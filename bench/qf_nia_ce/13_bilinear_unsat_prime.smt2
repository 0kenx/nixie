;; expected: unsat
; x*y = 7 with 1 ≤ x,y ≤ 3 (7 prime → no factors in box)
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 1) (<= x 3) (>= y 1) (<= y 3) (= (* x y) 7)))
(check-sat)
