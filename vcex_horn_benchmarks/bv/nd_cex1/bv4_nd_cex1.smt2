;// filepath: /home/daniel/Projects/cex/examples/smt/rep/simple_01.smt2
;// filepath: /home/daniel/Projects/cex/examples/smt/rep/simple_01.smt2
(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)

(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) 
  (=> (and (= x #b0000) (= y #b0000)) (inv x y))
))
(assert (forall ((x0 (_ BitVec 4)) (y0 (_ BitVec 4)) (x1 (_ BitVec 4)) (y1 (_ BitVec 4))) 
  (=> (and (inv x0 y0)
    (or 
      (= x1 (bvadd x0 #b0001))
      (= y1 (bvadd y0 #b0001)))
    )
    (inv x1 y1)
  )
))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) 
  (=> (and (inv x y) (not (and (< (+ 1 (bv2int x)) 16) (< (+ 1 (bv2int y)) 16)))) false)
))

(check-sat)
(exit)