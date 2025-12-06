(define-fun x_at_i ((i Int)) (_ BitVec 256)
  ((_ int2bv 256) i)
)

(declare-const trace (Array Int (_ BitVec 256)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 115792089237316195423570985008687907853269984665640564039457584007913129639935)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
