; Mixed CEX: x usually increments by 1, but can jump to any value
; Models a system with a "normal" path plus nondeterministic resets/jumps

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 1 OR x' = anything (nondeterministic jump)
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x01))
                 true))  ; Can also jump to any value
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
