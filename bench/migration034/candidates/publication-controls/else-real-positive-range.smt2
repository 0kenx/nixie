(set-logic UFLRA)(declare-fun f (Real) Real)(assert (forall ((x Real)) (>= (f x) 10.0)))(assert (= (f 0.0) 20.0))(check-sat)(get-model)(get-value ((f 0.0) (f 1.0)))
