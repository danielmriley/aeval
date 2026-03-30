; Reset CEX: x increments OR resets to 0
; This creates infinite loops that can be escaped by never resetting

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 1 OR x' = 0 (nondeterministic reset)
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x1))
                 (= x_next #x0)))
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
