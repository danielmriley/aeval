; Compact CEX for 256-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 256 bits of (i shifted left by 1)
; Trace bounds: 0 to 2^255-1

(define-fun x_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) (bvshl i #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000001))
)

(declare-const trace (Array (_ BitVec 512) (_ BitVec 256)))

(assert 
  (forall ((i (_ BitVec 512))) 
    (=> (and (bvule #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000000000000000000000000000000000007fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
