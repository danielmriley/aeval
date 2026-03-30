; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., 65536-2, then violates property
; Property: zext(x)+2 < 65536 (violated when x = 65536-2)
; Trace: 0 to 32767

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000)
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (= x_next (bvadd x #x0002)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 65536
(assert 
  (forall ((x (_ BitVec 16)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 16) x) #x00000002) #x00010000)))
        false)
  )
)

(check-sat)
