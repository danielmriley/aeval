;// filepath: bv16_cex1.smt2
; (set-logic HORN)
(declare-fun inv ((_ BitVec 16)) Bool)

(assert (forall ((x (_ BitVec 16))) 
  (=> (= x #b0000000000000000) (inv x))
))
(assert (forall ((x0 (_ BitVec 16)) (x1 (_ BitVec 16))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b0000000000000001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 16))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 65536))) false)
))

(check-sat)
(exit)
