;; expected: sat
; x² ≥ 4 with 1 ≤ x ≤ 5
(set-logic QF_NIA)
(declare-const x Int)
(assert (and (>= x 1) (<= x 5) (>= (* x x) 4)))
(check-sat)
