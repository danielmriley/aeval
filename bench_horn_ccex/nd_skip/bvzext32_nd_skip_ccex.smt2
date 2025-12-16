; CCEX for nd_skip: linear path (all +1 steps)
; For large bit widths, using simple x = i path
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
