(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun y_at_i ((i (_ BitVec 32))) (_ BitVec 16) 
  (let ((n ((_ extract 15 0) i)))
    (ite (bvult i #x00000fa0)
         n
         (ite (bvult i #x00001388)
              (bvsub (bvshl n (_ bv2 16)) (_ bv12000 16))
              (ite (bvult i #x00001770)
                   (bvsub (_ bv28000 16) (bvshl n (_ bv2 16)))
                   (bvsub (_ bv10000 16) n)
              )
         )
    )
  )
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00002715)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00002715)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)

(check-sat)
