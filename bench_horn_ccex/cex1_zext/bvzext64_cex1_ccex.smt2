; Compact CEX for 64-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 64 bits from 128-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 18446744073709551616

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 128))) (_ BitVec 128)
  i
)

(declare-const trace_x (Array (_ BitVec 128) (_ BitVec 64)))
(declare-const trace_counter (Array (_ BitVec 128) (_ BitVec 128)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x00000000000000010000000000000000)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
