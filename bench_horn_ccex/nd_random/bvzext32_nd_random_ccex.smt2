; CCEX for nd_random: explicit enumeration of random path
; This is NOT a closed-form function - it enumerates each step explicitly
; Values: [0, 2746317213, 478163327, 107420369, 3184935163, 1181241943, 1051802512, 958682846, 599310825, 3163119785, 440213415, 2906402157, 3181143731, 3831882064, 2342331444, 4294967295]
; Trace bounds: 0 to 15

(define-fun x_at_i ((i (_ BitVec 64))) (_ BitVec 32)
  (ite (= i #x000000000000000f) #xffffffff
    (ite (= i #x000000000000000e) #x8b9d2434
    (ite (= i #x000000000000000d) #xe465e150
    (ite (= i #x000000000000000c) #xbd9c66b3
    (ite (= i #x000000000000000b) #xad3c2d6d
    (ite (= i #x000000000000000a) #x1a3d1fa7
    (ite (= i #x0000000000000009) #xbc8960a9
    (ite (= i #x0000000000000008) #x23b8c1e9
    (ite (= i #x0000000000000007) #x392456de
    (ite (= i #x0000000000000006) #x3eb13b90
    (ite (= i #x0000000000000005) #x46685257
    (ite (= i #x0000000000000004) #xbdd640fb
    (ite (= i #x0000000000000003) #x06671ad1
    (ite (= i #x0000000000000002) #x1c80317f
    (ite (= i #x0000000000000001) #xa3b1799d
    #x00000000)))))))))))))))
)

(declare-const trace (Array (_ BitVec 64) (_ BitVec 32)))

(assert 
  (forall ((i (_ BitVec 64))) 
    (=> (and (bvule #x0000000000000000 i) (bvule i #x000000000000000f)) 
        (= (select trace i) (x_at_i i))
    )
  )
)

(check-sat)
