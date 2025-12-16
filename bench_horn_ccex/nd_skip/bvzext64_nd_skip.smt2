; Constrained nondeterministic: x' = x+1 OR x' = x+3
; Must reach exactly 18446744073709551615 to violate property
; Requires specific sequence of +1 and +3 choices

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: x' = x + 1 OR x' = x + 3
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x0000000000000001))
                 (= x_next (bvadd x #x0000000000000003))))
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
