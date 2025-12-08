; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., 256-1, then violates property
; Property: zext(x)+1 < 256
; Trace: 0 to 250

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 5
(assert 
  (inv #x05)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (= x_next (bvadd x #x01)))
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
