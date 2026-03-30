; CCEX for nd_skip k=16: shortest path using all +3 steps
; x(0) = 0, x(i) = 3*i (mod 2^16)
; Reaches 65535 in exactly 21845 steps (65535 = 21845 * 3)
; Trace bounds: 0 to 21845 (= (2^16 - 1) / 3 = 0x5555)

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  (bvmul ((_ extract 15 0) i) #x0003)
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert
  (forall ((i (_ BitVec 32)))
    (=> (and (bvule #x00000000 i) (bvule i #x00005555))
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
