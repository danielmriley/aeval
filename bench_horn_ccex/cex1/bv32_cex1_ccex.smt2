(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  i
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 32)))


(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #xffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
