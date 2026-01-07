; CCEX for Polynomial: x(i) = i^2
; c(i) = i
; x(i) = i*i
; Trace bounds: 0 to 255

(define-fun c_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  (bvmul i i)
)

(declare-const trace_c (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
