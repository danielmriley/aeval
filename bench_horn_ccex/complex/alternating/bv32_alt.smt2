; Alternating: x = i if even, -i if odd
; State: (c, x)
; Trans: c' = c + 1, x' = if (c' % 2 == 0) then c' else -c'

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
             (= x_next (ite (= (bvand c_next #x00000001) #x00000000) 
                            c_next 
                            (bvneg c_next))))
        (inv c_next x_next))
  )
)

; Error at max steps
(assert 
  (forall ((c (_ BitVec 32)) (x (_ BitVec 32)))
    (=> (and (inv c x) 
             (= x #x00000001))
        false)
  )
)

(check-sat)
