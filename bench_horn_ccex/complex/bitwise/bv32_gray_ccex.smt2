; CCEX for Gray Code
; c(i) = i
; x(i) = i ^ (i >> 1)

(define-fun c_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  i
)

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  (bvxor i (bvlshr i #x00000001))
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
