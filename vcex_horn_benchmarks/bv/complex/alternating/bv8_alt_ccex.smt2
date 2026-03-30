; CCEX for Alternating
; c(i) = i
; x(i) = ite(i & 1 == 0, i, -i)

(define-fun c_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  (ite (= (bvand i #x01) #x00) i (bvneg i))
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
