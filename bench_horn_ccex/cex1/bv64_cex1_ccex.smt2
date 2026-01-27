(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 64)
  i
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 64)))


(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #xffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
