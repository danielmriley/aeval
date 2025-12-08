; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < 2^32 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < 2^32
; This ensures x' = x+2 will satisfy zext(x')+2 < 2^32
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000004) #x0000000100000000)
             (= x_next (bvadd x #x00000002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 2^32
(assert 
  (forall ((x (_ BitVec 32)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000002) #x0000000100000000)))
        false)
  )
)

(check-sat)
