(set-logic ALL)
(set-option :random-seed 79190)

      (declare-const a (Array (_ BitVec 7) (_ BitVec 7)))
      (declare-const k (_ BitVec 7))
      (assert (and (forall ((k (_ BitVec 7))) (forall ((k (_ BitVec 7))) (= k k)))
        (forall ((i (_ BitVec 7))) (= (select (store a i k) (_ bv1 7)) k))))
      (check-sat)(get-model)
