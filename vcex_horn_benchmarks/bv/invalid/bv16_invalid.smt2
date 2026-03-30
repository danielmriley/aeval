; Linear counter x' = x + 1
(set-logic HORN)
(declare-fun inv ((_ BitVec 16)) Bool)
(assert (forall ((x (_ BitVec 16))) (=> (= x #x0000) (inv x))))
(assert (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x) (bvult x #xffff) (= x_next (bvadd x #x0001))) (inv x_next))))
(assert (forall ((x (_ BitVec 16))) (=> (and (inv x) (= x #xffff)) false)))
(check-sat)
