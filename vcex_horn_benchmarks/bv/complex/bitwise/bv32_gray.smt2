; Bitwise pattern: Gray Code x = i ^ (i >> 1)
; State: (c, x)
; Trans: c' = c + 1, x' = c' ^ (c' >> 1)

(set-logic HORN)

(declare-fun inv ((_ BitVec 32) (_ BitVec 32)) Bool)

; Init: c=0, x=0
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
             (= x_next (bvxor c_next (bvlshr c_next #x00000001))))
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
