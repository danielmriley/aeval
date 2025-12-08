; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 16 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 16
; Guard: zext(x)+2 < 16 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 15-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 16
; This ensures the NEXT state x' will satisfy zext(x')+1 < 16
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 4) x) #x02) #x10)
             (= x_next (bvadd x #x1)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 16
(assert 
  (forall ((x (_ BitVec 4)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 4) x) #x01) #x10)))
        false)
  )
)

(check-sat)
