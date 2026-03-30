; Saturation: x = min(i, 32768)
; State: (c, x)
; Trans: c' = c + 1, x' = if x < 32768 then x + 1 else x

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Init
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)))
    (=> (and (= c #x0000) (= x #x0000)) (inv c x))
  )
)

; Trans
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)) 
           (c_next (_ BitVec 16)) (x_next (_ BitVec 16)))
    (=> (and (inv c x)
             (bvult c #xffff)
             (= c_next (bvadd c #x0001))
             (= x_next (ite (bvult x #x8000) (bvadd x #x0001) x)))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)))
    (=> (and (inv c x) 
             (= x #x8000))
        false)
  )
)

(check-sat)
