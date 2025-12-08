; Compact CEX for 16-bit cex3_zext: three variables, all increment by 1
; x_at_i(i) = y_at_i(i) = z_at_i(i) = extract(i)
; Trace bounds: 0 to 65535

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun y_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun z_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_z (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000ffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i))
             (= (select trace_z i) (z_at_i i)))
    )
  )
)

(check-sat)
