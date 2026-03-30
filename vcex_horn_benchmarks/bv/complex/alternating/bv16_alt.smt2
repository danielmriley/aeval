; Alternating: x = i if even, -i if odd
; State: (c, x)
; Trans: c' = c + 1, x' = if (c' % 2 == 0) then c' else -c'

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
             (= x_next (ite (= (bvand c_next #x0001) #x0000) 
                            c_next 
                            (bvneg c_next))))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 16)) (x (_ BitVec 16)))
    (=> (and (inv c x) 
             (= x #x0001))
        false)
  )
)

(check-sat)
