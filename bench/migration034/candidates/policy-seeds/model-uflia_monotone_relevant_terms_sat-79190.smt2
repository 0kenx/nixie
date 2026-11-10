
        (set-logic UFLIA)
(set-option :random-seed 79190)

        (declare-fun f (Int) Int)
        (assert (forall ((x Int) (y Int)) (=> (<= x y) (<= (f x) (f y)))))
        (assert (= (f 0) 0))
        (assert (= (f 10) 100))
        (assert (>= (f 5) 30))
        (assert (<= (f 5) 70))
        (check-sat)(get-model)
    
(get-model)
