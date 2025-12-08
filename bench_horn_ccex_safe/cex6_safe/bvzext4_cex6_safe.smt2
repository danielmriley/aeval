; SAFE zero-extend version of cex6: x starts at 5, increments by 1
; The transition only fires when zext(x)+2 < 16 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 5
(assert 
  (inv #x5)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 16
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
