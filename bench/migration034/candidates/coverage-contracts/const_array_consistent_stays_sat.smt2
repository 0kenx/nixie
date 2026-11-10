
        (set-logic QF_ANIA)
        (declare-const a (Array Int Int))
        (declare-const i Int)
        (assert (= a ((as const (Array Int Int)) 5)))
        (assert (= (select a i) 5))
        (check-sat)
    
(get-model)
