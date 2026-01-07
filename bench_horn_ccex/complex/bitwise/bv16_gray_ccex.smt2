; CCEX for Gray Code
; c(i) = i
; x(i) = i ^ (i >> 1)

(define-fun c_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  (bvxor i (bvlshr i #x0001))
)

(declare-const trace_c (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
