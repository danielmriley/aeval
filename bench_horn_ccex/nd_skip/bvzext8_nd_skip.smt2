; Constrained nondeterministic: x' = x+1 OR x' = x+3
; Must reach exactly 255 to violate property
; Requires specific sequence of +1 and +3 choices

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 1 OR x' = x + 3
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (or (= x_next (bvadd x #x01))
                 (= x_next (bvadd x #x03))))
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
