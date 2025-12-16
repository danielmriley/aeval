; CCEX for nd_skip: linear path (all +1 steps)
; For large bit widths, using simple x = i path
; Trace bounds: 0 to 255

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  ((_ extract 7 0) i)
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x00ff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
