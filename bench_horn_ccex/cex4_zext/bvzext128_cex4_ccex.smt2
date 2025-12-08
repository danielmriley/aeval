; Compact CEX for 128-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 128 bits of (i shifted left by 1)
; Trace bounds: 0 to 2^127-1

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) (bvshl i #x0000000000000000000000000000000000000000000000000000000000000001))
)

(declare-const trace (Array (_ BitVec 256) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x000000000000000000000000000000007fffffffffffffffffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
