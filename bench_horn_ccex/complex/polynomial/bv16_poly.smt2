; Polynomial growth: x = i^2
; State: (c, x) where c is counter, x is c^2
; Trans: c' = c + 1, x' = x + 2c + 1
; Bound: c < 255 (approx 2^(k/2))

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Init: c=0, x=0
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)))
    (=> (and (= c #x0000) (= x #x0000)) (inv c x))
  )
)

; Trans: c' = c+1, x' = x + 2c + 1
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)) 
           (c_next (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv c x)
             (= c_next (bvadd c #x0001))
             (= x_next (bvadd x (bvadd (bvmul #x0002 c) #x0001))))
        (inv c_next x_next))
  )
)

; Property: x reaches max_steps^2
; We check if we can reach the state where x = max_steps^2
; The negation is: if x = max_steps^2 then false
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)))
    (=> (and (inv c x) 
             (= x #xfe01))
        false)
  )
)

(check-sat)
