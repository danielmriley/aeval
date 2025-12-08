; SAFE zero-extend version of cex6: x starts at 5, increments by 1
; The transition only fires when zext(x)+2 < 2^32 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 5
(assert 
  (inv #x00000005)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 2^32
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
