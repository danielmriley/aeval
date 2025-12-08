; Compact CEX for 128-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 2^128-6

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) (bvadd i #x0000000000000000000000000000000000000000000000000000000000000005))
)

(declare-const trace (Array (_ BitVec 256) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000fffffffffffffffffffffffffffffffa)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
