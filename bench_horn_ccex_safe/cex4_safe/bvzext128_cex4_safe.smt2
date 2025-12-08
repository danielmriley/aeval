; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < 2^128 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 128)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000000000000000000000000000)
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < 2^128
; This ensures x' = x+2 will satisfy zext(x')+2 < 2^128
(assert 
  (forall ((x (_ BitVec 128)) (x_next (_ BitVec 128)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000004) #x0000000000000000000000000000000100000000000000000000000000000000)
             (= x_next (bvadd x #x00000000000000000000000000000002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 2^128
(assert 
  (forall ((x (_ BitVec 128)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000002) #x0000000000000000000000000000000100000000000000000000000000000000)))
        false)
  )
)

(check-sat)
