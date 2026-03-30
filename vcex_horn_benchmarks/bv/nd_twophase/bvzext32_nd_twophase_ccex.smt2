; CCEX for nd_twophase: x = i, y = max(0, i - 2^31)
; x follows linear path
; y is 0 until i >= 2^31, then y = i - 2^31
; Trace bounds: 0 to 4294967295

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(define-fun y_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  (ite (bvult i #x0000000080000000)
    #x00000000
    ((_ extract 31 0) (bvsub i #x0000000080000000))
  )
)

(declare-const trace_x (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const trace_y (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000ffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
