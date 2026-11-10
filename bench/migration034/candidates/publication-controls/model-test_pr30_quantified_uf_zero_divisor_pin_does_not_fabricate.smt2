
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const y Int)
        (assert (forall ((z Int)) (>= (f z) 0)))
        (assert (= y 1))
        (assert (not (= (f y) (f (div 1 0)))))
        (check-sat)(get-model)
    
(get-model)
