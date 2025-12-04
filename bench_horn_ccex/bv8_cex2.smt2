;// 8-bit version of bv4_cex2
(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
  (=> (and (= x #x00) (= y #x00)) (inv x y))
))
(assert (forall ((x0 (_ BitVec 8)) (y0 (_ BitVec 8)) (x1 (_ BitVec 8)) (y1 (_ BitVec 8))) 
  (=> (and (inv x0 y0)
        (= x1 (bvadd x0 #x01))
        (= y1 (bvadd y0 #x01)))
    (inv x1 y1)
  )
))
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8))) 
  (=> (and (inv x y) (not (and (< (+ 1 (bv2int x)) 256) (< (+ 1 (bv2int y)) 256)))) false)
))

(check-sat)
(exit)
