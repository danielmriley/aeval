; Constrained nondeterministic: x' = x+1 OR x' = x+3
; Must reach exactly 4294967295 to violate property
; Requires specific sequence of +1 and +3 choices

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' = x + 1 OR x' = x + 3
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x00000001))
                 (= x_next (bvadd x #x00000003))))
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
