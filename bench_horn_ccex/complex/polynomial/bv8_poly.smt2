; Polynomial growth: x = i^2
; State: (c, x) where c is counter, x is c^2
; Trans: c' = c + 1, x' = x + 2c + 1
; Bound: c < 15 (approx 2^(k/2))

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Init: c=0, x=0
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)))
    (=> (and (= c #x00) (= x #x00)) (inv c x))
  )
)

; Trans: c' = c+1, x' = x + 2c + 1
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)) 
           (c_next (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv c x)
             (= c_next (bvadd c #x01))
             (= x_next (bvadd x (bvadd (bvmul #x02 c) #x01))))
        (inv c_next x_next))
  )
)

; Property: x reaches max_steps^2
; We check if we can reach the state where x = max_steps^2
; The negation is: if x = max_steps^2 then false
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)))
    (=> (and (inv c x) 
             (= x #xe1))
        false)
  )
)

(check-sat)
