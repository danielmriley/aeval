; Compact CEX for 16-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 16 bits of 32-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 65535 (65536 states)

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000ffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
