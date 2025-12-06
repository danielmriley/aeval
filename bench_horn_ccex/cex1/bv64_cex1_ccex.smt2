(define-fun x_at_i ((i Int)) (_ BitVec 64)
  ((_ int2bv 64) i)
)

(declare-const trace (Array Int (_ BitVec 64)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 18446744073709551615)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
