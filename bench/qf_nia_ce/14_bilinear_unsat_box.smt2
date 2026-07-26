;; expected: unsat
; x*y = 13 with 2 ≤ x,y ≤ 3 (no factor pair in box)
(set-logic QF_NIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 2) (<= x 3) (>= y 2) (<= y 3) (= (* x y) 13)))
(check-sat)
