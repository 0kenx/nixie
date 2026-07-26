;; expected: sat
; 2x = 6 with 1 ≤ x ≤ 9 (linear)
(set-logic QF_LIA)
(declare-const x Int)
(assert (and (>= x 1) (<= x 9) (= (* x 2) 6)))
(check-sat)
