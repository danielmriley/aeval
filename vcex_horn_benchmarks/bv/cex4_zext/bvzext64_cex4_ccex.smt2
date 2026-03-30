; Compact CEX for 64-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 64 bits of (i shifted left by 1)
; Trace bounds: 0 to 2^63-1

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) (bvshl i #x00000000000000000000000000000001))
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x00000000000000007fffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
