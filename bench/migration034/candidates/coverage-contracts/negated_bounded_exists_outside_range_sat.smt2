
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (not (exists ((x Int)) (and (>= x 0) (<= x 2) (= (f x) 7)))))
        (assert (= (f 3) 7))
        (check-sat)
    
(get-model)
