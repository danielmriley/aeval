; Saturation: x = min(i, 128)
; State: (c, x)
; Trans: c' = c + 1, x' = if x < 128 then x + 1 else x

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Init
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)))
    (=> (and (= c #x00) (= x #x00)) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)) 
           (c_next (_ BitVec 8)) (x_next (_ BitVec 8)))
    (=> (and (inv c x)
             (bvult c #xff)
             (= c_next (bvadd c #x01))
             (= x_next (ite (bvult x #x80) (bvadd x #x01) x)))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)))
    (=> (and (inv c x) 
             (= x #x80))
        false)
  )
)

(check-sat)
