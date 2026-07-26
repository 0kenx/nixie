;; expected: sat
; 24 ≤ a*b*c*d ≤ 30 with 1 ≤ each ≤ 5
(set-logic QF_NIA)
(declare-const a Int)
(declare-const b Int)
(declare-const c Int)
(declare-const d Int)
(assert (and
  (>= a 1) (<= a 5) (>= b 1) (<= b 5)
  (>= c 1) (<= c 5) (>= d 1) (<= d 5)
  (>= (* a b c d) 24) (<= (* a b c d) 30)))
(check-sat)
