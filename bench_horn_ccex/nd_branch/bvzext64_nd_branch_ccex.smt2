; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., 18446744073709551615
; Trace bounds: 0 to 2^63

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  (ite (= i #x00000000000000000000000000000000)
    (_ bv0 64)
    (bvsub (bvshl ((_ extract 63 0) i) (_ bv1 64)) (_ bv1 64))
  )
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x00000000000000008000000000000000)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
