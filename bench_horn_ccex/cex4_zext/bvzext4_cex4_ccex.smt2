; Compact CEX for 4-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 4 bits of (i shifted left by 1)
; Trace bounds: 0 to 7

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) (bvshl i #x01))
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x07)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
