; Polynomial growth: x = i^2
; State: (c, x) where c is counter, x is c^2
; Trans: c' = c + 1, x' = x + 2c + 1
; Bound: c < 65535 (approx 2^(k/2))

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Init: c=0, x=0
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (= c #x00000000) (= x #x00000000)) (inv c x))
  )
)

; Trans: c' = c+1, x' = x + 2c + 1
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)) 
           (c_next (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv c x)
             (= c_next (bvadd c #x00000001))
             (= x_next (bvadd x (bvadd (bvmul #x00000002 c) #x00000001))))
        (inv c_next x_next))
  )
)

; Property: x reaches max_steps^2
; We check if we can reach the state where x = max_steps^2
; The negation is: if x = max_steps^2 then false
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (inv c x) 
             (= x #xfffe0001))
        false)
  )
)

(check-sat)
