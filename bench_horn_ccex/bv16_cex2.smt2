;// 16-bit version of bv4_cex2
(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

(assert (forall ((x (_ BitVec 16)) (y (_ BitVec 16))) 
  (=> (and (= x #x0000) (= y #x0000)) (inv x y))
))
(assert (forall ((x0 (_ BitVec 16)) (y0 (_ BitVec 16)) (x1 (_ BitVec 16)) (y1 (_ BitVec 16))) 
  (=> (and (inv x0 y0)
        (= x1 (bvadd x0 #x0001))
        (= y1 (bvadd y0 #x0001)))
    (inv x1 y1)
  )
))
(assert (forall ((x (_ BitVec 16)) (y (_ BitVec 16))) 
  (=> (and (inv x y) (not (and (< (+ 1 (bv2int x)) 65536) (< (+ 1 (bv2int y)) 65536)))) false)
))

(check-sat)
(exit)
