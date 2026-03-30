; Bitwise pattern: Gray Code x = i ^ (i >> 1)
; State: (c, x)
; Trans: c' = c + 1, x' = c' ^ (c' >> 1)

(set-logic HORN)

(declare-fun inv ((_ BitVec 16) (_ BitVec 16)) Bool)

; Init: c=0, x=0
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
             (= x_next (bvxor c_next (bvlshr c_next #x0001))))
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
