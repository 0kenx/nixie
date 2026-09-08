(set-logic QF_FP)
(set-info :status unsat)
(assert (= ((_ to_fp 3 4) RNE (/ 31.0 16.0)) (fp #b0 #b001 #b000)))
(check-sat)
