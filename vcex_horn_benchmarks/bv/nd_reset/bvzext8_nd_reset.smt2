; Reset CEX: x increments OR resets to 0
; This creates infinite loops that can be escaped by never resetting

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 1 OR x' = 0 (nondeterministic reset)
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x01))
                 (= x_next #x00)))
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
