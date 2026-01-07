; Linear counter x' = x + 1
(set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)
(assert (forall ((x (_ BitVec 8))) (=> (= x #x00) (inv x))))
(assert (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x) (bvult x #xff) (= x_next (bvadd x #x01))) (inv x_next))))
(assert (forall ((x (_ BitVec 8))) (=> (and (inv x) (= x #xff)) false)))
(check-sat)
