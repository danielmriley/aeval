; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., 2^32-1, then violates property
; Property: zext(x)+1 < 2^32
; Trace: 0 to 2^32-6

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 5
(assert 
  (inv #x00000005)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (= x_next (bvadd x #x00000001)))
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
