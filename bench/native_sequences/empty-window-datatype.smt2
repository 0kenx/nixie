; Two representations of the same empty sequence remain distinct datatypes.
(set-logic ALL)
(set-info :status sat)
(declare-datatype W ((win (off Int) (len Int) (graph (Array Int Int)))))
(declare-const a (Array Int Int))
(assert (distinct (win 0 0 a) (win 1 0 a)))
(check-sat)
