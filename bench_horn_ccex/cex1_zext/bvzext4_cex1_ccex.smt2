; Compact CEX for 4-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 4 bits from 8-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 16

(define-fun x_at_i ((i (_ BitVec 8))) (_ BitVec 4)
  ((_ extract 3 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 8))) (_ BitVec 8)
  i
)

(declare-const trace_x (Array (_ BitVec 8) (_ BitVec 4)))
(declare-const trace_counter (Array (_ BitVec 8) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 8))) 
    (=> (and (bvule #x00 i) (bvule i #x10)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
