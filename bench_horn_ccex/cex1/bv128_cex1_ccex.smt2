(define-fun x_at_i ((i Int)) (_ BitVec 128)
  ((_ int2bv 128) i)
)

(declare-const trace (Array Int (_ BitVec 128)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 340282366920938463463374607431768211455)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
