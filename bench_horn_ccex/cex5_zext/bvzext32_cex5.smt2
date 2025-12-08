; Zero-extend version of cex5: x += 1, y += 2
; y overflows first at step 2^31-1
; Property: zext(x)+1 < 2^32 AND zext(y)+2 < 2^32
; Trace: 0 to 2^31-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
    (=> (and (= x #x00000000) (= y #x00000000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)) 
           (x_next (_ BitVec 32)) (y_next (_ BitVec 32)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x00000001))
             (= y_next (bvadd y #x00000002)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^32 AND zext(y)+2 < 2^32
(assert 
  (forall ((x (_ BitVec 32)) (y (_ BitVec 32)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000001) #x0000000100000000)
                       (bvult (bvadd ((_ zero_extend 32) y) #x0000000000000002) #x0000000100000000))))
        false)
  )
)

(check-sat)
