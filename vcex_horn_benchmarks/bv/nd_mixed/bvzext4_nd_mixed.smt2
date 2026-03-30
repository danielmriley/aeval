; Mixed CEX: x usually increments by 1, but can jump to any value
; Models a system with a "normal" path plus nondeterministic resets/jumps

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 1 OR x' = anything (nondeterministic jump)
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x1))
                 true))  ; Can also jump to any value
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
