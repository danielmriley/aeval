; Branching CEX: (x mod 2 = 0) ? x+1 : x+2
; Even x: increment by 1
; Odd x: increment by 2
; Path: 0 → 1 → 3 → 5 → 7 → ... → 4294967295

(set-logic HORN)

(declare-fun inv ((_ BitVec 32)) Bool)

; Initial state: x = 0
(assert 
  (inv #x00000000)
)

; Transition: if LSB is 0 (even) then x+1 else x+2
(assert 
  (forall ((x (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv x)
             (or (and (= ((_ extract 0 0) x) #b0) (= x_next (bvadd x #x00000001)))
                 (and (= ((_ extract 0 0) x) #b1) (= x_next (bvadd x #x00000002)))))
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
