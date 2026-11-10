(set-logic ALL)
(set-option :random-seed 47514)
(declare-const m Int)(assert (forall ((x Int)) (or (<= x 7) (= m 1))))(assert (= m 2))(check-sat)
