;// filepath: bv8_cex1.smt2
; (set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8))) 
  (=> (= x #b00000000) (inv x))
))
(assert (forall ((x0 (_ BitVec 8)) (x1 (_ BitVec 8))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b00000001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 8))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 256))) false)
))

(check-sat)
(exit)
