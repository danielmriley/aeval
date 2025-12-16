; Branching CEX: (x mod 2 = 0) ? x+1 : x+2
; Even x: increment by 1
; Odd x: increment by 2
; Path: 0 → 1 → 3 → 5 → 7 → ... → 18446744073709551615

(set-logic HORN)

(declare-fun inv ((_ BitVec 64)) Bool)

; Initial state: x = 0
(assert 
  (inv #x0000000000000000)
)

; Transition: if LSB is 0 (even) then x+1 else x+2
(assert 
  (forall ((x (_ BitVec 64)) (x_next (_ BitVec 64)))
    (=> (and (inv x)
             (or (and (= ((_ extract 0 0) x) (_ bv0 1)) (= x_next (bvadd x #x0000000000000001)))
                 (and (= ((_ extract 0 0) x) (_ bv1 1)) (= x_next (bvadd x #x0000000000000002)))))
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
