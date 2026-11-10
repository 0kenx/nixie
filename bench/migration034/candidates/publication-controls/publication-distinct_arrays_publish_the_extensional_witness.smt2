(set-logic QF_ABV)
        (declare-const a (Array (_ BitVec 1) (_ BitVec 1)))
        (declare-const b (Array (_ BitVec 1) (_ BitVec 1)))
        (assert (distinct a b)) (check-sat) (get-model)
