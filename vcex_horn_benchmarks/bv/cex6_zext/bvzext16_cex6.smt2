; Zero-extend version of cex6: x starts at 5, increments by 1
; x goes: 5, 6, 7, ..., 65536-1, then violates property
; Property: zext(x)+1 < 65536
; Trace: 0 to 65530

(set-logic HORN)

(declare-fun inv ((_ BitVec 16)) Bool)

; Initial state: x = 5
(assert 
  (inv #x0005)
)

; Transition: x' = x + 1
(assert 
  (forall ((x (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv x)
             (= x_next (bvadd x #x0001)))
        (inv x_next))
  )
)

; Property: zext(x)+1 < 65536
(assert 
  (forall ((x (_ BitVec 16)))
    (=> (and (inv x) 
             (not (bvult (bvadd ((_ zero_extend 16) x) #x00000001) #x00010000)))
        false)
  )
)

(check-sat)
