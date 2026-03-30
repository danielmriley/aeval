; CCEX for nd_reset: linear path (always increment, never reset)
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
