;; expected: sat
; f,g defined by nested ite tables; f(i)*g(j) = 6
(set-logic QF_NIA)
(declare-const i Int)
(declare-const j Int)
(define-fun f ((k Int)) Int
  (ite (= k 1) 3 (ite (= k 2) 4 (ite (= k 3) 6 0))))
(define-fun g ((k Int)) Int
  (ite (= k 1) 2 (ite (= k 2) 3 0)))
(assert (and (>= i 1) (<= i 3) (>= j 1) (<= j 3) (= (* (f i) (g j)) 6)))
(check-sat)
