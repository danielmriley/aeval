; Compact CEX for 256-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 2^256-6

(define-fun x_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) (bvadd i #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000005))
)

(declare-const trace (Array (_ BitVec 512) (_ BitVec 256)))

(assert 
  (forall ((i (_ BitVec 512))) 
    (=> (and (bvule #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x0000000000000000000000000000000000000000000000000000000000000000fffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffa)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
