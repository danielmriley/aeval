; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., 255
; Trace bounds: 0 to 128

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  (ite (= i #x0000)
    (_ bv0 8)
    (bvsub (bvshl ((_ extract 7 0) i) (_ bv1 8)) (_ bv1 8))
  )
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x0080)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
