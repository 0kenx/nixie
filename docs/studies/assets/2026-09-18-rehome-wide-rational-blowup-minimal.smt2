(set-logic QF_LIRA)
(declare-const xi Int)
(assert (and (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3)) (not (and (>= (+ (+ (* 2 xi) (* -1 xi) 62) (+ -2147483648 -4611686018427387904)) (mod (* 10 xi) 7)))) (not (or (< (* 10 xi) (div (* 3 xi) 7))))))))
(check-sat)
