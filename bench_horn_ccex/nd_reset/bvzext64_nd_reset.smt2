; Reset CEX: x increments OR resets to 0
; This creates infinite loops that can be escaped by never resetting

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: x' = x + 1 OR x' = 0 (nondeterministic reset)
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x0000000000000001))
                 (= x_next #x0000000000000000)))
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
