; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 65536 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 65536
; Guard: zext(x)+2 < 65536 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 65535-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 65536
; This ensures the NEXT state x' will satisfy zext(x')+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 16) x) #x00000002) #x00010000)
             (= x_next (bvadd x #x0001)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)))
        false)
  )
)

(check-sat)
