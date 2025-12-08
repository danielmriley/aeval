; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., 2^32-2, then violates property
; Property: zext(x)+2 < 2^32 (violated when x = 2^32-2)
; Trace: 0 to 2^31-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (= x_next (bvadd x #x00000002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 2^32
(assert 
  (forall ((x (_ BitVec 32)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 32) x) #x0000000000000002) #x0000000100000000)))
        false)
  )
)

(check-sat)
