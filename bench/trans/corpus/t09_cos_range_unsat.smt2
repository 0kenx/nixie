(set-logic QF_NRT)
(declare-const x Real)
(assert (<= (cos x) -2.0))
(check-sat)
