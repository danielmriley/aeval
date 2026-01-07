; Alternating: x = i if even, -i if odd
; State: (c, x)
; Trans: c' = c + 1, x' = if (c' % 2 == 0) then c' else -c'

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
             (= x_next (ite (= (bvand c_next #x01) #x00) 
                            c_next 
                            (bvneg c_next))))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 8)) (x (_ BitVec 8)))
    (=> (and (inv c x) 
             (= x #x01))
        false)
  )
)

(check-sat)
