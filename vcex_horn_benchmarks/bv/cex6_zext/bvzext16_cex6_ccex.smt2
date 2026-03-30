; Compact CEX for 16-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 65530

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) (bvadd i #x00000005))
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000fffa)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
