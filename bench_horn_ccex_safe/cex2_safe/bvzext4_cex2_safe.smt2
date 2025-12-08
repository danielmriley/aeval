; SAFE zero-extend version of cex2: two variables x, y both increment by 1
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4) (_ BitVec 4)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
    (=> (and (= x #x0) (= y #x0)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1, ONLY when both next states satisfy property
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)) 
           (x_next (_ BitVec 4)) (y_next (_ BitVec 4)))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend 4) x) #x02) #x10)
             (bvult (bvadd ((_ zero_extend 4) y) #x02) #x10)
             (= x_next (bvadd x #x1))
             (= y_next (bvadd y #x1)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 16 AND zext(y)+1 < 16
(assert 
  (forall ((x (_ BitVec 4)) (y (_ BitVec 4)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 4) x) #x01) #x10)
                       (bvult (bvadd ((_ zero_extend 4) y) #x01) #x10))))
        false)
  )
)

(check-sat)
