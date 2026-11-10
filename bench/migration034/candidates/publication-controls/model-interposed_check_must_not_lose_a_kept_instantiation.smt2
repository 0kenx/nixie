
        (set-logic UFLIA)
        (declare-fun f (Int) Int)
        (declare-const k Int)
        (assert (forall ((i Int)) (=> (and (>= i 0) (<= i 3)) (= (f i) 0))))
        (assert (or (= k 1) (= k 2)))
        (check-sat)(get-model)(get-model)
        (assert (= (f 1) 9))
        (assert (= k 1))
        (check-sat)(get-model)(get-model)
    