; CCEX for nd_reset: linear path (always increment, never reset)
; Trace bounds: 0 to 65535

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  ((_ extract 15 0) i)
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000ffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
