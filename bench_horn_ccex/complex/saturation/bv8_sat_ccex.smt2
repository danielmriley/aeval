; CCEX for Saturation
; c(i) = i
; x(i) = ite(i < 128, i, 128)

(define-fun c_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  (ite (bvult i #x80) i #x80)
)

(declare-const trace_c (Array (_ BitVec 8) (_ BitVec 8)))
(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #xff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
