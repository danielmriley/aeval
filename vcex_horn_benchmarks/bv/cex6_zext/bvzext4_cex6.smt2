; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., 16-1, then violates property
; Property: zext(x)+1 < 16
; Trace: 0 to 10

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 5
(assert 
  (inv #x5)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (= x_next (bvadd x #x1)))
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
