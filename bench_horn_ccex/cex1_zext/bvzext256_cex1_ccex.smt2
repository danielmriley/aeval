; Compact CEX for 256-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 256 bits of 512-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 2^256-1 (2^256 states)

(define-fun x_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) i)
)

(declare-const trace (Array (_ BitVec 512) (_ BitVec 256)))

(assert 
  (forall ((i (_ BitVec 512))) 
    (=> (and (bvule #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x0000000000000000000000000000000000000000000000000000000000000000ffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
