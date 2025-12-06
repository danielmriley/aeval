; Compact CEX for 8-bit zero-extend benchmark
; Value functions:
;   x at step i = extract lower 8 bits from 16-bit index
;   counter at step i = i (the index itself)
; Trace bounds: 0 to 256

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(define-fun counter_at_i ((i (_ BitVec 16))) (_ BitVec 16)
  i
)

(declare-const trace_x (Array (_ BitVec 16) (_ BitVec 8)))
(declare-const trace_counter (Array (_ BitVec 16) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x0100)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_counter i) (counter_at_i i)))
    )
  )
)

(check-sat)
