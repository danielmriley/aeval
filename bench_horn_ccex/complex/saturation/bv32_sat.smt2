; Saturation: x = min(i, 2147483648)
; State: (c, x)
; Trans: c' = c + 1, x' = if x < 2147483648 then x + 1 else x

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Init
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (= c #x00000000) (= x #x00000000)) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)) 
           (c_next (_ BitVec 32)) (x_next (_ BitVec 32)))
    (=> (and (inv c x)
             (bvult c #xffffffff)
             (= c_next (bvadd c #x00000001))
             (= x_next (ite (bvult x #x80000000) (bvadd x #x00000001) x)))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (inv c x) 
             (= x #x80000000))
        false)
  )
)

(check-sat)
