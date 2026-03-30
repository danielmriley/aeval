; Random-path CEX: x can take ANY value at each step
; This models a system with completely nondeterministic transitions
; The CCEX must enumerate explicit values for each step

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' can be ANY value (completely nondeterministic)
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (inv x)
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
