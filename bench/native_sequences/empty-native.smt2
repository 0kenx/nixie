(set-logic ALL)
(set-info :status unsat)
(assert (distinct (seq.extract (seq.unit 1) 1 0) (as seq.empty (Seq Int))))
(check-sat)
