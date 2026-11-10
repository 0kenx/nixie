(set-logic UFLIA)(declare-fun f (Int) Int)(declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= y 1))(assert (distinct (f y) (f (div 1 0))))
        (check-sat)(get-model)(get-value ((div 1 0) (div 7 0) (distinct (f y) (f (div 1 0)))))
