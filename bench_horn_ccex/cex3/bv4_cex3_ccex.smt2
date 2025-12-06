(define-fun x_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) i)
)
(define-fun y_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) i)
)
(define-fun z_at_i ((i Int)) (_ BitVec 4)
  ((_ int2bv 4) i)
)

(declare-const trace_x (Array Int (_ BitVec 4)))
(declare-const trace_y (Array Int (_ BitVec 4)))
(declare-const trace_z (Array Int (_ BitVec 4)))


(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 15)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)
(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 15)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)
(assert 
  (forall ((i Int)) 
    (=> (and (<= 0 i) (<= i 15)) 
        (= (select trace_z i) (z_at_i i))
    )
  )
)

(check-sat)