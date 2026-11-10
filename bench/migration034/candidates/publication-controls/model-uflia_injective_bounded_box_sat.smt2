
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (assert (forall ((x Int) (y Int))
          (=> (and (>= x 0) (<= x 10) (>= y 0) (<= y 10) (= (f x) (f y)))
              (= x y))))
        (assert (= (f 1) 10))
        (assert (= (f 2) 20))
        (assert (= (f 3) 30))
        (check-sat)(get-model)
    
(get-model)
