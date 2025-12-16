; Compact CEX for s_split_01 (unsafe version)
; x increments by 1 from 0
; y stays 5000 until x >= 5000, then increments (so y=x for x>=5000)
; Trace bounds: 0 to 10000

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(define-fun y_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  (ite (bvult i #x00001388)
       #x1388
       ((_ extract 15 0) i))
)

(declare-const trace_x (Array (_ BitVec 32) (_ BitVec 16)))
(declare-const trace_y (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x00002710)) 
        (and (= (select trace_x i) (x_at_i i))
             (= (select trace_y i) (y_at_i i)))
    )
  )
)

(check-sat)
