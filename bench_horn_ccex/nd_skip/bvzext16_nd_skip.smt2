; Constrained nondeterministic: x' = x+1 OR x' = x+3
; Must reach exactly 65535 to violate property
; Requires specific sequence of +1 and +3 choices

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' = x + 1 OR x' = x + 3
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x0001))
                 (= x_next (bvadd x #x0003))))
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
