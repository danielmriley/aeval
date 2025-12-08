; Zero-extend version of cex5: x += 1, y += 2
; y overflows first at step 2^127-1
; Property: zext(x)+1 < 2^128 AND zext(y)+2 < 2^128
; Trace: 0 to 2^127-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 128) (_ BitVec 128)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 128)) (y (_ BitVec 128)))
    (=> (and (= x #x00000000000000000000000000000000) (= y #x00000000000000000000000000000000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 2
(assert 
  (forall ((x (_ BitVec 128)) (y (_ BitVec 128)) 
           (x_next (_ BitVec 128)) (y_next (_ BitVec 128)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x00000000000000000000000000000001))
             (= y_next (bvadd y #x00000000000000000000000000000002)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^128 AND zext(y)+2 < 2^128
(assert 
  (forall ((x (_ BitVec 128)) (y (_ BitVec 128)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000001) #x0000000000000000000000000000000100000000000000000000000000000000)
                       (bvult (bvadd ((_ zero_extend 128) y) #x0000000000000000000000000000000000000000000000000000000000000002) #x0000000000000000000000000000000100000000000000000000000000000000))))
        false)
  )
)

(check-sat)
