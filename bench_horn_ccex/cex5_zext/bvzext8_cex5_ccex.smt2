; Compact CEX for 8-bit cex5_zext: x += 1, y += 2
; x_at_i(i) = extract(i), y_at_i(i) = extract(i << 1)
; Trace bounds: 0 to 127

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun y_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) (bvshl i #x0001))
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_y (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x007f)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
