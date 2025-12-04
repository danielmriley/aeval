;// 8-bit version of bv4_cex1
; (set-logic HORN)
(declare-fun inv ((_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8))) 
  (=> (= x #x00) (inv x))
))
(assert (forall ((x0 (_ BitVec 8)) (x1 (_ BitVec 8))) 
  (=> (and (inv x0)
        (= x1 (bvadd x0 #x01)))
    (inv x1)
  )
))
(assert (forall ((x (_ BitVec 8))) 
  (=> (and (inv x) (not (< (+ 1 (bv2int x)) 256))) false)
))

(check-sat)
