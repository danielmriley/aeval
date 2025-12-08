; SAFE zero-extend version of cex2: two variables x, y both increment by 1
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (= x #x0000) (= y #x0000)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1, ONLY when both next states satisfy property
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)) 
           (x_next (_ BitVec 16)) (y_next (_ BitVec 16)))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend 16) x) #x00000002) #x00010000)
             (bvult (bvadd ((_ zero_extend 16) y) #x00000002) #x00010000)
             (= x_next (bvadd x #x0001))
             (= y_next (bvadd y #x0001)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 65536 AND zext(y)+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (y (_ BitVec 16)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)
                       (bvult (bvadd ((_ zero_extend 16) y) #x00000001) #x00010000))))
        false)
  )
)

(check-sat)
