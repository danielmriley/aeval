(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)
(define-fun y_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)
(define-fun z_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_z (Array (_ BitVec 16) (_ BitVec 16)))


(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)
(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (= (select trace_y i) (y_at_i i))
    )
  )
)
(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (= (select trace_z i) (z_at_i i))
    )
  )
)
