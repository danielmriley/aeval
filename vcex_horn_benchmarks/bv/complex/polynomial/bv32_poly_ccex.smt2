; CCEX for Polynomial: x(i) = i^2
; c(i) = i
; x(i) = i*i
; Trace bounds: 0 to 65535

(define-fun c_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  i
)

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  (bvmul i i)
)

(declare-const trace_c (Array (_ BitVec 32) (_ BitVec 32)))
(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000ffff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
