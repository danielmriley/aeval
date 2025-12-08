; Compact CEX for 4-bit cex2_zext: two variables, both increment by 1
; x_at_i(i) = extract(i), y_at_i(i) = extract(i)
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(define-fun y_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 4)))
(declare-const trace_y (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0f)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
