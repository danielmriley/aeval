; Compact CEX for 64-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 2^64-6

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) (bvadd i #x00000000000000000000000000000005))
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x0000000000000000fffffffffffffffa)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
