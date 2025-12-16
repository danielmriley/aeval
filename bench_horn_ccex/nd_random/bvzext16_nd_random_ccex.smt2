; CCEX for nd_random: explicit enumeration of random path
; This is NOT a closed-form function - it enumerates each step explicitly
; Values: [0, 41905, 7296, 1639, 48598, 18024, 16049, 14628, 9144, 48265, 6717, 44348, 48540, 58469, 35741, 65535]
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 32))) (_ BitVec 16)
  (ite (= i #x0000000f) #xffff
    (ite (= i #x0000000e) #x8b9d
    (ite (= i #x0000000d) #xe465
    (ite (= i #x0000000c) #xbd9c
    (ite (= i #x0000000b) #xad3c
    (ite (= i #x0000000a) #x1a3d
    (ite (= i #x00000009) #xbc89
    (ite (= i #x00000008) #x23b8
    (ite (= i #x00000007) #x3924
    (ite (= i #x00000006) #x3eb1
    (ite (= i #x00000005) #x4668
    (ite (= i #x00000004) #xbdd6
    (ite (= i #x00000003) #x0667
    (ite (= i #x00000002) #x1c80
    (ite (= i #x00000001) #xa3b1
    #x0000)))))))))))))))
)

(declare-const trace (Array (_ BitVec 32) (_ BitVec 16)))

(assert 
  (forall ((i (_ BitVec 32))) 
    (=> (and (bvule #x00000000 i) (bvule i #x0000000f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
