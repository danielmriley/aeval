;// 16-bit version of bv4_cex1
; (set-logic HORN)
(declare-fun inv ((_ BitVec 16)) Bool)

(assert (forall ((x (_ BitVec 16))) 
  (=> (= x #x0000) (inv x))
))
(assert (forall ((x0 (_ BitVec 16)) (x1 (_ BitVec 16))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #x0001)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 16))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 65536))) false)
))

(check-sat)
