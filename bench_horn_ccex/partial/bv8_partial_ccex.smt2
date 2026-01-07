; PARTIAL CCEX: Only defines x(i)
; y and z are missing, but not needed for property violation
(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)
(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 8)))
; trace_y and trace_z are intentionally missing
(assert (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #xff)) 
        (= (select trace_x i) (x_at_i i)))))
(check-sat)
