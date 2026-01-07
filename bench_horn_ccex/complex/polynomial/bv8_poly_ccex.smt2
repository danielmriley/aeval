; CCEX for Polynomial: x(i) = i^2
; c(i) = i
; x(i) = i*i
; Trace bounds: 0 to 15

(define-fun c_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  (bvmul i i)
)

(declare-const trace_c (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0f)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
