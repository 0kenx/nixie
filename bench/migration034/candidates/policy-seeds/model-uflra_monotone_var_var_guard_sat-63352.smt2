
        (set-logic UFLRA)
(set-option :random-seed 63352)

        (declare-fun f (Real) Real)
        (assert (forall ((x Real) (y Real)) (=> (<= x y) (<= (f x) (f y)))))
        (assert (= (f 0.0) 0.0))
        (assert (= (f 1.0) 2.5))
        (assert (= (f 3.0) 7.0))
        (check-sat)(get-model)
    
(get-model)
