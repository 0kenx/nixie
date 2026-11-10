
    (set-logic UFLIA)
    (declare-fun f (Int) Int)
    (declare-const x Int)
    (assert (or (= x 1) (= x 2) (= x 3)))
    (assert (forall ((i Int)) (=> (= x i) (> (f i) 10))))
    (assert (< (f 1) 5))
    (assert (< (f 2) 5))

(check-sat)(get-model)(get-model)
