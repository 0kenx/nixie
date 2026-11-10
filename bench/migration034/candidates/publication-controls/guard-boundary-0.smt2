(set-logic ALL)(assert (forall ((x Int)) (=> (distinct x 3) false)))(check-sat)
