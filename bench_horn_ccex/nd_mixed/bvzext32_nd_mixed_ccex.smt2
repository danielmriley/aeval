; CCEX for nd_mixed: simple linear path x = i
; Even though the system allows jumps, the linear path is a valid witness
; Trace bounds: 0 to 4294967295

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  ((_ extract 31 0) i)
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x00000000ffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
