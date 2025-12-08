; SAFE zero-extend version of cex1: single variable x, with loop guard
; The transition only fires when zext(x)+2 < 2^64 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)
;
; Property: zext(x)+1 < 2^64
; Guard: zext(x)+2 < 2^64 (ensures x' = x+1 will satisfy property)
; Guard prevents transition when x >= 2^64-1-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 2^64
; This ensures the NEXT state x' will satisfy zext(x')+1 < 2^64
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000002) #x00000000000000010000000000000000)
             (= x_next (bvadd x #x0000000000000001)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 2^64
(assert 
  (forall ((x (_ BitVec 64)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 64) x) #x00000000000000000000000000000001) #x00000000000000010000000000000000)))
        false)
  )
)

(check-sat)
