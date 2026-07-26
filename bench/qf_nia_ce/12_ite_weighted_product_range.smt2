;; expected: sat
; Nested ite tables for p,q,r; product range constraint
(set-logic QF_NIA)
(declare-const i Int)
(declare-const h Int)
(define-fun p ((k Int)) Int (ite (= k 1) 30 (ite (= k 2) 32 0)))
(define-fun q ((k Int)) Int (ite (= k 1) 76 (ite (= k 2) 74 0)))
(define-fun r0 ((k Int)) Int 5)
(define-fun abs_i ((x Int)) Int (ite (< x 0) (- x) x))
(define-fun r ((k Int) (t Int)) Int
  (let ((d (abs_i (- t (r0 k)))))
    (ite (<= d 3) 10 (ite (<= d 6) 6 0))))
(assert (and
  (>= i 1) (<= i 2) (>= h 1) (<= h 9)
  (>= (* (p i) (q i) (r i h) 10) 200000)
  (<= (* (p i) (q i) (r i h) 10) 300000)))
(check-sat)
