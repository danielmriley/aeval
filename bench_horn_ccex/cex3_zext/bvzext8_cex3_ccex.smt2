; Compact CEX for 8-bit cex3_zext: three variables, all increment by 1
; x_at_i(i) = y_at_i(i) = z_at_i(i) = extract(i)
; Trace bounds: 0 to 255

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun y_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun z_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_y (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_z (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i))
             (= (select trace_z i) (z_at_i i)))
    )
  )
)

(check-sat)
