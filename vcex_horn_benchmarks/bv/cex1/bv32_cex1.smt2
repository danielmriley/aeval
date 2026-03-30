;// filepath: bv32_cex1.smt2
; (set-logic HORN)
(declare-fun inv ((_ BitVec 32)) Bool)

(assert (forall ((x (_ BitVec 32))) 
  (=> (= x #b00000000000000000000000000000000) (inv x))
))
(assert (forall ((x0 (_ BitVec 32)) (x1 (_ BitVec 32))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b00000000000000000000000000000001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 32))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 4294967296))) false)
))

(check-sat)
(exit)
