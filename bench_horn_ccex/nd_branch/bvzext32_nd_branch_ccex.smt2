; CCEX for nd_branch: parity-based path
; x(0) = 0, x(i) = 2*i - 1 for i >= 1
; Path: 0, 1, 3, 5, 7, ..., 4294967295
; Trace bounds: 0 to 2^31

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  (ite (= i #x0000000000000000)
    #x00000000
    (bvsub (bvshl ((_ extract 31 0) i) #x00000001) #x00000001)
  )
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x0000000080000000)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
