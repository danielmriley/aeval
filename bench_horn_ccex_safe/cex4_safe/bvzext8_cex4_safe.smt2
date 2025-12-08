; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < 256 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < 256
; This ensures x' = x+2 will satisfy zext(x')+2 < 256
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 8) x) #x0004) #x0100)
             (= x_next (bvadd x #x02)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 256
(assert 
  (forall ((x (_ BitVec 8)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)))
        false)
  )
)

(check-sat)
