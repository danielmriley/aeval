; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., 15
; Trace bounds: 0 to 8

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  (ite (= i #x00)
    (_ bv0 4)
    (bvsub (bvshl ((_ extract 3 0) i) (_ bv1 4)) (_ bv1 4))
  )
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x08)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
