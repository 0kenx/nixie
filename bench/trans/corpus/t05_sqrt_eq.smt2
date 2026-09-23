(set-logic QF_NRT)
(declare-const x Real)
(assert (= (sqrt x) 2.0))
(check-sat)
