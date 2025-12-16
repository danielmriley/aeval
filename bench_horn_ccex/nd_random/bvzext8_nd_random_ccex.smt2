; CCEX for nd_random: explicit enumeration of random path
; This is NOT a closed-form function - it enumerates each step explicitly
; Values: [0, 163, 28, 6, 189, 70, 62, 57, 35, 188, 26, 173, 189, 228, 139, 255]
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 16))) (_ BitVec 8)
  (ite (= i #x000f) #xff
    (ite (= i #x000e) #x8b
    (ite (= i #x000d) #xe4
    (ite (= i #x000c) #xbd
    (ite (= i #x000b) #xad
    (ite (= i #x000a) #x1a
    (ite (= i #x0009) #xbc
    (ite (= i #x0008) #x23
    (ite (= i #x0007) #x39
    (ite (= i #x0006) #x3e
    (ite (= i #x0005) #x46
    (ite (= i #x0004) #xbd
    (ite (= i #x0003) #x06
    (ite (= i #x0002) #x1c
    (ite (= i #x0001) #xa3
    #x00)))))))))))))))
)

(declare-const trace (Array (_ BitVec 16) (_ BitVec 8)))

(assert 
  (forall ((i (_ BitVec 16))) 
    (=> (and (bvule #x0000 i) (bvule i #x000f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
