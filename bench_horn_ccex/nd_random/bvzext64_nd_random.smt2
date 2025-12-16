; Random-path CEX: x can take ANY value at each step
; This models a system with completely nondeterministic transitions
; The CCEX must enumerate explicit values for each step

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: x' can be ANY value (completely nondeterministic)
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (inv x)
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
