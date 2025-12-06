(define-fun x_at_i ((i Int)) (_ BitVec 16)
  ((_ int2bv 16) i)
)

(declare-const trace (Array Int (_ BitVec 16)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 65535)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
