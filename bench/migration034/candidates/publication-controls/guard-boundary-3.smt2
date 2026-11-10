(set-logic ALL)(declare-fun f (Int) Int)(assert (forall ((i Int)) (=> (< i 5) (= (f i) 0))))(assert (= (f 4) 1))(check-sat)
