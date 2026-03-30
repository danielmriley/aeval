; Compact CEX for 4-bit cex6_zext: x starts at 5, increments by 1
; x_at_i(i) = 5 + i = extract(i + 5)
; Trace bounds: 0 to 10

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) (bvadd i #x05))
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0a)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
