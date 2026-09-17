(set-logic QF_LIRA)
(declare-const xi Int)
(assert (and (not (and (not (or (> (+ (mod (mod 3 2) 7) (+ (* -2 xi) (- (* 1 xi) -2) (* 1 xi))) -6) (> (mod (+ (div 9223372036854775807 4) (+ (* 5 xi) (* 3 xi) 0) (mod -3 4)) 5) (* -1 xi)))) (>= (+ (* 10 xi) (- (* 5 xi) -2) (* 5 xi)) (mod (+ (- (* 1 xi) 2) (* 10 xi) (* 2 xi)) 3)))) (> (* 2 xi) 4) (= (+ (* -1 xi) (div (+ -21 (* 2 xi)) 4)) -66)))
(check-sat)
