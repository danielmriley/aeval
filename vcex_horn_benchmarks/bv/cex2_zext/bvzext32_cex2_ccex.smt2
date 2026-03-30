; Compact CEX for 32-bit cex2_zext: two variables, both increment by 1
; x_at_i(i) = extract(i), y_at_i(i) = extract(i)
; Trace bounds: 0 to 2^32-1

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(define-fun y_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(declare-const trace_x (Array (_ BitVec 64) (_ BitVec 32)))
(declare-const trace_y (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000ffffffff)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
