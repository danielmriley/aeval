; Compact CEX for 128-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 128 bits of 256-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 2^128-1 (2^128 states)

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(declare-const trace (Array (_ BitVec 256) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000ffffffffffffffffffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
