; Zero-extend version of cex4: single variable x incrementing by 2
; x goes: 0, 2, 4, 6, ..., 16-2, then violates property
; Property: zext(x)+2 < 16 (violated when x = 16-2)
; Trace: 0 to 7

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: x' = x + 2
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (= x_next (bvadd x #x2)))
        (inv x_next))
  )
)

; Property: zext(x)+2 < 16
(assert 
  (forall ((x (_ BitVec 4)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 4) x) #x02) #x10)))
        false)
  )
)

(check-sat)
