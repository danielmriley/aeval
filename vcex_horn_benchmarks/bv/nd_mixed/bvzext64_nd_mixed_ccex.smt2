; CCEX for nd_mixed: simple linear path x = i
; Even though the system allows jumps, the linear path is a valid witness
; Trace bounds: 0 to 18446744073709551615

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  ((_ extract 63 0) i)
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert 
  (forall ((i (_ BitVec 128))) 
    (=> (and (bvule #x00000000000000000000000000000000 i) (bvule i #x0000000000000000ffffffffffffffff)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
