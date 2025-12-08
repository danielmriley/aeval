; Compact CEX for 128-bit cex5_zext: x += 1, y += 2
; x_at_i(i) = extract(i), y_at_i(i) = extract(i << 1)
; Trace bounds: 0 to 2^127-1

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(define-fun y_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) (bvshl i #x0000000000000000000000000000000000000000000000000000000000000001))
)

(declare-const trace_x (Array (_ BitVec 256) (_ BitVec 128)))
(declare-const trace_y (Array (_ BitVec 256) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x000000000000000000000000000000007fffffffffffffffffffffffffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
