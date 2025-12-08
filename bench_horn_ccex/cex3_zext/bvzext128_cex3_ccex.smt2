; Compact CEX for 128-bit cex3_zext: three variables, all increment by 1
; x_at_i(i) = y_at_i(i) = z_at_i(i) = extract(i)
; Trace bounds: 0 to 2^128-1

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(define-fun y_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(define-fun z_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(declare-const trace_x (Array (_ BitVec 256) (_ BitVec 128)))
(declare-const trace_y (Array (_ BitVec 256) (_ BitVec 128)))
(declare-const trace_z (Array (_ BitVec 256) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000ffffffffffffffffffffffffffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i))
             (= (select trace_z i) (z_at_i i)))
    )
  )
)

(check-sat)
