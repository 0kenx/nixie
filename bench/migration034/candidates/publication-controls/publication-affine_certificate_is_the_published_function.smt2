(set-logic UFLRA)
        (declare-fun f (Real) Real)
        (assert (forall ((x Real)) (= (f x) (+ (* 2.0 x) 1.0))))
        (check-sat)(get-model)(get-value ((f 3.0) (f (- 2.0))))
