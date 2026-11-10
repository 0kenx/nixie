(set-logic UFLIA)(declare-fun f (Int) Int)(assert (forall ((x Int)) (>= (f x) 10)))(assert (= (f 0) 20))(check-sat)(get-model)(get-value ((f 0) (f 1)))
