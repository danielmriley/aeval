; Compact CEX for 64-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 64 bits of 128-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 2^64-1 (2^64 states)

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) i)
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x0000000000000000ffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
