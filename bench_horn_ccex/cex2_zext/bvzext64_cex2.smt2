; Zero-extend version of cex2: two variables x, y both increment by 1
; Property: zext(x)+1 < 2^64 AND zext(y)+1 < 2^64
; Trace: 0 to 2^64-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 64) (_ BitVec 64)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (= x #x0000000000000000) (= y #x0000000000000000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)) 
           (x_next (_ BitVec 64)) (y_next (_ BitVec 64)))
    (=> (and (inv x y)
             (= x_next (bvadd x #x0000000000000001))
             (= y_next (bvadd y #x0000000000000001)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 2^64 AND zext(y)+1 < 2^64
(assert 
  (forall ((x (_ BitVec 64)) (y (_ BitVec 64)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000001) #x00000000000000010000000000000000)
                       (bvult (bvadd ((_ zero_extend 64) y) #x00000000000000000000000000000001) #x00000000000000010000000000000000))))
        false)
  )
)

(check-sat)
