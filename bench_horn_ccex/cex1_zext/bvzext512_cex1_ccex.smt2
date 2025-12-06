; Compact CEX for 512-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 512 bits of 1024-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 2^512-1 (2^512 states)

(define-fun x_at_i ((i (_ BitVec 1024))) (_ BitVec 512)
  ((_ extract 511 0) i)
)

(declare-const trace (Array (_ BitVec 1024) (_ BitVec 512)))

(assert 
  (forall ((i (_ BitVec 1024))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
