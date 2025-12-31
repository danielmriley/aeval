(define-fun x_at_i ((i Int)) (_ BitVec 8)
  ((_ int2bv 8) i)
)

(declare-const trace_x (Array Int (_ BitVec 8)))

(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 255)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)

(check-sat)
