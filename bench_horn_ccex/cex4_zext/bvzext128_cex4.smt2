; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., 2^128-2, then violates property
; Property: zext(x)+2 < 2^128 (violated when x = 2^128-2)
; Trace: 0 to 2^127-1

(set-logic HORN)

(declare-fun inv ((_ BitVec 128)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000000000000000000000000000)
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec 128)) (x_next (_ BitVec 128)))
    (=> (and (inv x)
             (= x_next (bvadd x #x00000000000000000000000000000002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 2^128
(assert 
  (forall ((x (_ BitVec 128)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 128) x) #x0000000000000000000000000000000000000000000000000000000000000002) #x0000000000000000000000000000000100000000000000000000000000000000)))
        false)
  )
)

(check-sat)
