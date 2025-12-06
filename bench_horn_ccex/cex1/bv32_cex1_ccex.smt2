(define-fun x_at_i ((i Int)) (_ BitVec 32)
  ((_ int2bv 32) i)
)

(declare-const trace (Array Int (_ BitVec 32)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 4294967295)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
