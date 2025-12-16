; Branching CEX: (x mod 2 = 0) ? x+1 : x+2
; Even x: increment by 1
; Odd x: increment by 2
; Path: 0 → 1 → 3 → 5 → 7 → ... → 15

(set-logic HORN)

(declare-fun inv ((_ BitVec 4)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0)
)

; Transition: if LSB is 0 (even) then x+1 else x+2
(assert 
  (forall ((x (_ BitVec 4)) (x_next (_ BitVec 4)))
    (=> (and (inv x)
             (or (and (= ((_ extract 0 0) x) (_ bv0 1)) (= x_next (bvadd x #x1)))
                 (and (= ((_ extract 0 0) x) (_ bv1 1)) (= x_next (bvadd x #x2)))))
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
