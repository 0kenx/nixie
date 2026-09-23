(set-logic QF_NRT)
(declare-const x Real)
(assert (>= (atan x) 1.0))
(check-sat)
