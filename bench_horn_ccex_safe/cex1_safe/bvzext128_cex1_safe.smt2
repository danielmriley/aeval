; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 2^128 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 2^128
; Guard: zext(x)+2 < 2^128 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 2^128-1-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 128)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000000000000000000000000000)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 2^128
; This ensures the NEXT state x' will satisfy zext(x')+1 < 2^128
(assert 
  (forall ((x (_ BitVec 128)) (x_next (_ BitVec 128)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000002) #x0000000000000000000000000000000100000000000000000000000000000000)
             (= x_next (bvadd x #x00000000000000000000000000000001)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 2^128
(assert 
  (forall ((x (_ BitVec 128)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000001) #x0000000000000000000000000000000100000000000000000000000000000000)))
        false)
  )
)

(check-sat)
