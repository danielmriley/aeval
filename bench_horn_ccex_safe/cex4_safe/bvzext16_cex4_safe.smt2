; SAFE zero-extend version of cex4: single variable x incrementing by 2
; The transition only fires when zext(x)+4 < 65536 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' = x + 2, ONLY when zext(x)+4 < 65536
; This ensures x' = x+2 will satisfy zext(x')+2 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 16) x) #x00000004) #x00010000)
             (= x_next (bvadd x #x0002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 65536
(assert 
  (forall ((x (_ BitVec 16)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 16) x) #x00000002) #x00010000)))
        false)
  )
)

(check-sat)
