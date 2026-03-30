;// filepath: bv64_cex1.smt2
; (set-logic HORN)
(declare-fun inv ((_ BitVec 64)) Bool)

(assert (forall ((x (_ BitVec 64))) 
  (=> (= x #b0000000000000000000000000000000000000000000000000000000000000000) (inv x))
))
(assert (forall ((x0 (_ BitVec 64)) (x1 (_ BitVec 64))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #b0000000000000000000000000000000000000000000000000000000000000001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 64))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 18446744073709551616))) false)
))

(check-sat)
(exit)
