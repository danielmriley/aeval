; Compact CEX for 8-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 8 bits of 16-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 255 (256 states)

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
