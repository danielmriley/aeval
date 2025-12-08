; Compact CEX for 32-bit cex5_zext: x += 1, y += 2
; x_at_i(i) = extract(i), y_at_i(i) = extract(i << 1)
; Trace bounds: 0 to 2^31-1

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(define-fun y_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) (bvshl i #x0000000000000001))
)

(declare-const trace_x (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const trace_y (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x000000007fffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
