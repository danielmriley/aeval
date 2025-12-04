(define-fun x_at_i ((i Int)) (_ BitVec 8)
  ((_ int2bv 8) i)
)

(declare-const trace (Array Int (_ BitVec 8)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 256)) 
        (= (select trace i) (x_at_i i))
    )
  )
)
