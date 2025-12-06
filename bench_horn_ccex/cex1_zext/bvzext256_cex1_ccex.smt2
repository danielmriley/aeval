; Compact CEX for 256-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 256 bits from 512-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 2^256

(define-fun x_at_i ((i (_ BitVec 512))) (_ BitVec 256)
  ((_ extract 255 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 512))) (_ BitVec 512)
  i
)

(declare-const trace_x (Array (_ BitVec 512) (_ BitVec 256)))
(declare-const trace_counter (Array (_ BitVec 512) (_ BitVec 512)))

(assert 
  (forall ((i (_ BitVec 512))) 
    (=> (and (bvule #x00000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x00000000000000000000000000000000000000000000000000000000000000010000000000000000000000000000000000000000000000000000000000000000)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
