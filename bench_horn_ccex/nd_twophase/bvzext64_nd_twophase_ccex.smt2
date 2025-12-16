; CCEX for nd_twophase: x = i, y = max(0, i - 2^63)
; x follows linear path
; y is 0 until i >= 2^63, then y = i - 2^63
; Trace bounds: 0 to 18446744073709551615

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) i)
)

(define-fun y_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  (ite (bvult i #x00000000000000008000000000000000)
    #x0000000000000000
    ((_ extract 63 0) (bvsub i #x00000000000000008000000000000000))
  )
)

(declare-const trace_x (Array (_ BitVec 128) (_ BitVec 64)))
(declare-const trace_y (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x0000000000000000ffffffffffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
