; Compact CEX for 16-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 16 bits from 32-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 65536

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 32))) (_ BitVec 32)
  i
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_counter (Array (_ BitVec 32) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00010000)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
