; CCEX for Alternating
; c(i) = i
; x(i) = ite(i & 1 == 0, i, -i)

(define-fun c_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  i
)

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  (ite (= (bvand i #x00000001) #x00000000) i (bvneg i))
)

(declare-const trace_c (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #xffffffff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
