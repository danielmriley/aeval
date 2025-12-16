; Random-path CEX: x can take ANY value at each step
; This models a system with completely nondeterministic transitions
; The CCEX must enumerate explicit values for each step

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' can be ANY value (completely nondeterministic)
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (inv x)
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
