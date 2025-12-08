; Compact CEX for 16-bit cex4_zext: x increments by 2
; x_at_i(i) = 2*i = extract lower 16 bits of (i shifted left by 1)
; Trace bounds: 0 to 32767

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) (bvshl i #x00000001))
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00007fff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
