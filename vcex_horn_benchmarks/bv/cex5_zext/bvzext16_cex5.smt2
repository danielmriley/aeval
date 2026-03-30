; Zero-extend version of cex5: x += 1, y += 2
; y overflows first at step 32767
; Property: zext(x)+1 < 65536 AND zext(y)+2 < 65536
; Trace: 0 to 32767

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (= x #x0000) (= y #x0000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) 
           (x_next (_ BitVec 16)) (y_next (_ BitVec 16)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x0001))
             (= y_next (bvadd y #x0002)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 65536 AND zext(y)+2 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)
                       (bvult (bvadd ((_ zero_extend 16) y) #x00000002) #x00010000))))
        false)
  )
)

(check-sat)
