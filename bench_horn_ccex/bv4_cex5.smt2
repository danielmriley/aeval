;; Example 5: Two variables with different increments
;; x increments by 1, y increments by 2
;; x: 0, 1, 2, 3, ...
;; y: 0, 2, 4, 6, 8, 10, 12, 14, 0 (overflow at step 8)
(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)

(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) 
  (=> (and (= x #b0000) (= y #b0000)) (inv x y))
))
(assert (forall ((x0 (_ BitVec 4)) (y0 (_ BitVec 4)) (x1 (_ BitVec 4)) (y1 (_ BitVec 4))) 
  (=> (and (inv x0 y0)
        (= x1 (bvadd x0 #b0001))
        (= y1 (bvadd y0 #b0010)))
    (inv x1 y1)
  )
))
(assert (forall ((x (_ BitVec 4)) (y (_ BitVec 4))) 
  (=> (and (inv x y) (not (and (< (+ 1 (bv2int x)) 16) (< (+ 2 (bv2int y)) 16)))) false)
))

(check-sat)
