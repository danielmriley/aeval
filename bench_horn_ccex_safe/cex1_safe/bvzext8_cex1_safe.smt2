; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 256 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 256
; Guard: zext(x)+2 < 256 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 255-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 256
; This ensures the NEXT state x' will satisfy zext(x')+1 < 256
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)
             (= x_next (bvadd x #x01)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 256
(assert 
  (forall ((x (_ BitVec 8)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 8) x) #x0001) #x0100)))
        false)
  )
)

(check-sat)
