; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., 65535
; Trace bounds: 0 to 32768

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  (ite (= i #x00000000)
    (_ bv0 16)
    (bvsub (bvshl ((_ extract 15 0) i) (_ bv1 16)) (_ bv1 16))
  )
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00008000)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
