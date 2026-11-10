(set-logic ALL)
(set-option :random-seed 31676)
(declare-const m Int)(assert (forall ((x Int)) (or (<= x 7) (= m 1))))(push)(assert (= m 2))(check-sat)(pop)(assert (= m 1))(check-sat)(push)(assert (= m 2))(check-sat)(pop)(check-sat)
