; CCEX for nd_skip k=32: shortest path using all +3 steps
; x(0) = 0, x(i) = 3*i (mod 2^32)
; Reaches 2^32-1 in exactly 1431655765 steps (= (2^32-1)/3 = 0x55555555)
; Trace bounds: 0 to 1431655765

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  (bvmul ((_ extract 31 0) i) #x00000003)
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert
  (forall ((i (_ BitVec 64)))
    (=> (and (bvule #x0000000000000000 i) (bvule i #x0000000055555555))
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
