; CCEX for nd_twophase: x = i, y = max(0, i - 32768)
; x follows linear path
; y is 0 until i >= 32768, then y = i - 32768
; Trace bounds: 0 to 65535

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun y_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  (ite (bvult i #x00008000)
    #x0000
    ((_ extract 15 0) (bvsub i #x00008000))
  )
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000ffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
