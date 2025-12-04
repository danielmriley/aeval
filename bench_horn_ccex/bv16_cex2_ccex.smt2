(define-fun x_at_i ((i Int)) (_ BitVec 16)
  ((_ int2bv 16) i)
)
(define-fun y_at_i ((i Int)) (_ BitVec 16)
  ((_ int2bv 16) i)
)

(declare-const trace_x (Array Int (_ BitVec 16)))
(declare-const trace_y (Array Int (_ BitVec 16)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 65536)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)
(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 65536)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)
