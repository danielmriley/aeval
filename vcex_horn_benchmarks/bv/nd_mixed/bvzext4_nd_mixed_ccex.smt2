; CCEX for nd_mixed: simple linear path x = i
; Even though the system allows jumps, the linear path is a valid witness
; Trace bounds: 0 to 15

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
