;; expected: sat
; 3x + 2y = 12 with 1 ≤ x,y ≤ 9 (linear)
(set-logic QF_LIA)
(declare-const x Int)
(declare-const y Int)
(assert (and (>= x 1) (<= x 9) (>= y 1) (<= y 9) (= (+ (* 3 x) (* 2 y)) 12)))
(check-sat)
