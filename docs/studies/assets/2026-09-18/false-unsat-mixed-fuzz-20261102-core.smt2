(set-logic QF_LIRA)
(declare-const xi Int)
(assert (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3)) (not (and (>= (+ (+ (+ 2147483648 (* 3 xi) (* 3 xi)) (+ (* 2 xi) (* -1 xi) 62) (+ -92 (* -2 xi))) (+ (+ -2147483648 -4611686018427387904) (* 2 xi) (mod 5 7))) (mod (* 10 xi) 7)) (>= (mod (- (div (* 1 xi) 7) 2) 5) -6))))))
(check-sat)
