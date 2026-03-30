; Compact CEX for 32-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 32 bits of 64-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 2^32-1 (2^32 states)

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000ffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
