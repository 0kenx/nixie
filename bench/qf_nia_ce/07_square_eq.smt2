;; expected: sat
; x² = 9 with 1 ≤ x ≤ 9
(set-logic QF_NIA)
(declare-const x Int)
(assert (and (>= x 1) (<= x 9) (= (* x x) 9)))
(check-sat)
