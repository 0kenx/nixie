(set-logic QF_LIRA)
(declare-const xi Int)
(assert (and (not (or (= (mod (* 1 xi) 4) (div (- (+ 60 (* 2 xi) 20) 3) 3)) (not (and (>= (+ (+ (+ 2147483648 (* 3 xi) (* 3 xi)) (+ (* 2 xi) (* -1 xi) 62) (+ -92 (* -2 xi))) (+ (+ -2147483648 -4611686018427387904) (* 2 xi) (mod 5 7))) (mod (* 10 xi) 7)) (>= (mod (- (div (* 1 xi) 7) 2) 5) -6))) (not (or (> (mod (mod (* 3 xi) 5) 5) 71) (> (* 5 xi) 1) (< (+ (+ (+ (* 2 xi) (* 1 xi)) (+ -1 (* -2 xi) (* -1 xi)) (* 10 xi)) (+ (mod (* 2 xi) 1) (- (* 1 xi) 3) (+ 2 -5 6)) (* 10 xi)) (+ (+ (+ (* -2 xi) (* 2 xi)) (mod (* -2 xi) 1) -7) (+ (div (* 3 xi) 7) (+ (* 2 xi) (* 5 xi) (* 3 xi)))))))))))
(check-sat)
