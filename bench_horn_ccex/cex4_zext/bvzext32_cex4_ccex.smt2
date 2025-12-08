; Compact CEX for 32-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 32 bits of (i shifted left by 1)
; Trace bounds: 0 to 2^31-1

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) (bvshl i #x0000000000000001))
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x000000007fffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
