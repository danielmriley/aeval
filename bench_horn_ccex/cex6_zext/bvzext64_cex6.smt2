; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., 2^64-1, then violates property
; Property: zext(x)+1 < 2^64
; Trace: 0 to 2^64-6

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 5
(assert 
  (inv #x0000000000000005)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (= x_next (bvadd x #x0000000000000001)))
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
