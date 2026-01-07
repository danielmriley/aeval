; CCEX for Alternating
; c(i) = i
; x(i) = ite(i & 1 == 0, i, -i)

(define-fun c_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  (ite (= (bvand i #x0001) #x0000) i (bvneg i))
)

(declare-const trace_c (Array (_ BitVec 16) (_ BitVec 16)))
(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #xffff)) 
        (and (= (select trace_c i) (c_at_i i))
             (= (select trace_x i) (x_at_i i)))
    )
  )
)

(check-sat)
