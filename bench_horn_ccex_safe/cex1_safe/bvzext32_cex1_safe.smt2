; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 2^32 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 2^32
; Guard: zext(x)+2 < 2^32 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 2^32-1-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 2^32
; This ensures the NEXT state x' will satisfy zext(x')+1 < 2^32
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000002) #x0000000100000000)
             (= x_next (bvadd x #x00000001)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 2^32
(assert 
  (forall ((x (_ BitVec 32)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000001) #x0000000100000000)))
        false)
  )
)

(check-sat)
