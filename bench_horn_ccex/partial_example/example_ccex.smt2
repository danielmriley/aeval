(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)

(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #xff)) 
        (= (select trace_x i) (x_at_i i))
    )
  )
)

(check-sat)
