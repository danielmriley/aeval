;// filepath: bv4_cex1.smt2
; (set-logic HORN)
(declare-fun inv ((_ BitVec 4)) Bool)

(assert (forall ((x (_ BitVec 4))) 
  (=> (= x #b0000) (inv x))
))
(assert (forall ((x0 (_ BitVec 4)) (x1 (_ BitVec 4))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b0001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 4))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 16))) false)
))

(check-sat)
(exit)

