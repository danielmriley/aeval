; Compact CEX for 8-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 8 bits of (i shifted left by 1)
; Trace bounds: 0 to 127

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) (bvshl i #x0001))
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x007f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
