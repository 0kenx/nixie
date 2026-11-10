(declare-datatypes ((A 0) (B 0)) (((a1) (mkA (b B))) ((b1) (mkB (a A)))))
    (declare-const x1 A)(declare-const x2 A)(declare-const x3 A)
    (assert (distinct x1 x2 x3))
    (check-sat)(get-model)