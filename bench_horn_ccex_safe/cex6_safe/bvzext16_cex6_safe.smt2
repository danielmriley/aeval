; SAFE zero-extend version of cex6: x starts at 5, increments by 1
; The transition only fires when zext(x)+2 < 65536 (ensuring x' satisfies property)
; This means the property is ALWAYS satisfied (no CEX exists)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 5
(assert 
  (inv #x0005)
)

; Transition: x' = x + 1, ONLY when zext(x)+2 < 65536
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
