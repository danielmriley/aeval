; Mixed CEX: x usually increments by 1, but can jump to any value
; Models a system with a "normal" path plus nondeterministic resets/jumps

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: x' = x + 1 OR x' = anything (nondeterministic jump)
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x0000000000000001))
                 true))  ; Can also jump to any value
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
