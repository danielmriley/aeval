; Compact CEX for 32-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 2^32-6

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) (bvadd i #x0000000000000005))
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000fffffffa)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
