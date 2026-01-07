; Bitwise pattern: Gray Code x = i ^ (i >> 1)
; State: (c, x)
; Trans: c' = c + 1, x' = c' ^ (c' >> 1)

(set-logic HORN)

(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)

; Init: c=0, x=0
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
             (= x_next (bvxor c_next (bvlshr c_next #x01))))
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
