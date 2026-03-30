(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 16)))


(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
