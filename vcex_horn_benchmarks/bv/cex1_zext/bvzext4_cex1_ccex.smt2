; Compact CEX for 4-bit zero-extend benchmark
; Single variable x, BV index (replaces Int index from original)
;
; Value function: x at step i = extract(i) (lower 4 bits of 8-bit index)
; This is the BV equivalent of int2bv(i)
;
; Trace bounds: 0 to 15 (16 states)

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(declare-const trace (Array (_ BitVec 8) (_ BitVec 4)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x0f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
