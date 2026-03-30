(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)

(check-sat)
