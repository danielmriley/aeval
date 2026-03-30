; CCEX for nd_skip k=64: shortest path using all +3 steps
; x(0) = 0, x(i) = 3*i (mod 2^64)
; Reaches 2^64-1 in exactly 6148914691236517205 steps (= (2^64-1)/3 = 0x5555555555555555)
; Trace bounds: 0 to 6148914691236517205

(define-fun x_at_i ((i (_ BitVec 128))) (_ BitVec 64)
  (bvmul ((_ extract 63 0) i) #x0000000000000003)
)

(declare-const trace (Array (_ BitVec 128) (_ BitVec 64)))

(assert
  (forall ((i (_ BitVec 128)))
    (=> (and (bvule #x00000000000000000000000000000000 i)
             (bvule i #x00000000000000005555555555555555))
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
