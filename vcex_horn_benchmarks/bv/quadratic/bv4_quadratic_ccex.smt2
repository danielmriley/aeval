; CCEX for Quadratic Growth
; x(i) = i
; y(i) = i*(i-1)/2
; Trace bounds: 0 to 8 (fails at 8)

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(define-fun y_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) (bvlshr (bvmul i (bvsub i #x01)) #x01))
)

(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 4)))
(declare-const trace_y (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x08)) 
        (and
          (= (select trace_x i) (x_at_i i))
          (= (select trace_y i) (y_at_i i))
        )
    )
  )
)

(check-sat)
