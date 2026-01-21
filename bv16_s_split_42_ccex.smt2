(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun y_at_i ((i (_ BitVec 32))) (_ BitVec 16) 
  (let ((n ((_ extract 15 0) i)))
    (ite (bvult i #x000006e5) ;; n < 1765
         n
         (bvsub (bvmul n (_ bv2 16)) (_ bv1765 16)) ;; 2n - 1765
    )
  )
)

(define-fun z_at_i ((i (_ BitVec 32))) (_ BitVec 16) 
  (let ((n ((_ extract 15 0) i)))
    (ite (bvult i #x00000eb5) ;; n < 3765
         (bvmul n (_ bv2 16)) ;; 2n
         (bvsub (bvmul n (_ bv3 16)) (_ bv3765 16)) ;; 3n - 3765
    )
  )
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_z (Array (_ BitVec 32) (_ BitVec 16)))

;; Bound 18000 = #x4650
(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00004650)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00004650)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00004650)) 
        (= (select trace_z i) (z_at_i i))
    )
  )
)

(check-sat)
