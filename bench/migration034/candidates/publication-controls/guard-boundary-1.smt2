(set-logic ALL)(declare-const m Int)(assert (forall ((x Int)) (=> (>= x 10) (= m 1))))(assert (= m 2))(check-sat)
