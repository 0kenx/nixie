(set-logic QF_NRT)
(declare-const x Real)
(assert (>= (sin x) 2.0))
(check-sat)
