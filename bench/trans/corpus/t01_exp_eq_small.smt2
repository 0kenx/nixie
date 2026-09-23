(set-logic QF_NRT)
(declare-const x Real)
(assert (= (exp x) 2.0))
(check-sat)
