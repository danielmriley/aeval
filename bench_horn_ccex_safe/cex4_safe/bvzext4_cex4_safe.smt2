; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < 16 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < 16
; This ensures x' = x+2 will satisfy zext(x')+2 < 16
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 4) x) #x04) #x10)
             (= x_next (bvadd x #x2)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 16
(assert 
  (forall ((x (_ BitVec 4)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 4) x) #x02) #x10)))
        false)
  )
)

(check-sat)
