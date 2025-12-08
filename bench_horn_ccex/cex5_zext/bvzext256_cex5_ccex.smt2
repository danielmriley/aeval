; Compact CEX for 256-bit cex5_zext: x += 1, y += 2
; x_at_i(i) = extract(i), y_at_i(i) = extract(i << 1)
; Trace bounds: 0 to 2^255-1

(define-fun x_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) i)
)

(define-fun y_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) (bvshl i #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001))
)

(declare-const trace_x (Array (_ BitVec 512) (_ BitVec 256)))
(declare-const trace_y (Array (_ BitVec 512) (_ BitVec 256)))

(assert 
  (forall ((i (_ BitVec 512))) 
    (=> (and (bvule #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
