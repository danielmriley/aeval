; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., 256-2, then violates property
; Property: zext(x)+2 < 256 (violated when x = 256-2)
; Trace: 0 to 127

(set-logic HORN)

(declare-fun inv ((_ BitVec 8)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00)
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv x)
             (= x_next (bvadd x #x02)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 256
(assert 
  (forall ((x (_ BitVec 8)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 8) x) #x0002) #x0100)))
        false)
  )
)

(check-sat)
