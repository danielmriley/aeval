; PARTIAL CCEX: Only defines x(i)
; y and z are missing, but not needed for property violation
(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)
(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 16)))
; trace_y and trace_z are intentionally missing
(assert (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (= (select trace_x i) (x_at_i i)))))
(check-sat)
