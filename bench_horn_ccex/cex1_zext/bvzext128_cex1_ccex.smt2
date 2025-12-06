; Compact CEX for 128-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 128 bits from 256-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 2^128

(define-fun x_at_i ((i (_ BitVec 256))) (_ BitVec 128)
  ((_ extract 127 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 256))) (_ BitVec 256)
  i
)

(declare-const trace_x (Array (_ BitVec 256) (_ BitVec 128)))
(declare-const trace_counter (Array (_ BitVec 256) (_ BitVec 256)))

(assert 
  (forall ((i (_ BitVec 256))) 
    (=> (and (bvule #x0000000000000000000000000000000000000000000000000000000000000000 i) (bvule i #x0000000000000000000000000000000100000000000000000000000000000000)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
