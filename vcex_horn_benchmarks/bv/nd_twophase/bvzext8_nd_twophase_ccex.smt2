; CCEX for nd_twophase: x = i, y = max(0, i - 128)
; x follows linear path
; y is 0 until i >= 128, then y = i - 128
; Trace bounds: 0 to 255

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun y_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  (ite (bvult i #x0080)
    #x00
    ((_ extract 7 0) (bvsub i #x0080))
  )
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_y (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
