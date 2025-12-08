; SAFE zero-extend version of cex2: two variables x, y both increment by 1
; The transition only fires when BOTH next states satisfy the property
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Initial state: x = 0, y = 0
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (= x #x00) (= y #x00)) (inv x y))
  )
)

; Transition: x' = x + 1, y' = y + 1, ONLY when both next states satisfy property
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) 
           (x_next (_ BitVec 8)) (y_next (_ BitVec 8)))
    (=> (and (inv x y)
             (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)
             (bvult (bvadd ((_ zero_extend 8) y) #x0002) #x0100)
             (= x_next (bvadd x #x01))
             (= y_next (bvadd y #x01)))
        (inv x_next y_next))
  )
)

; Property: zext(x)+1 < 256 AND zext(y)+1 < 256
(assert 
  (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
    (=> (and (inv x y) 
             (not (and (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)
                       (bvult (bvadd ((_ zero_extend 8) y) #x0001) #x0100))))
        false)
  )
)

(check-sat)
