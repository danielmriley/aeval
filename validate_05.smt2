
(set-logic BV)
(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) (bvadd n #x0001))
(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16) (bvshl (bvsub n #x000a) #x0001))
(define-fun fz ((n (_ BitVec 16))) (_ BitVec 16) (let ((_let_1 (bvshl #b0000000000000001 (bvsub n #b0000000000001010)))) (ite (bvuge (bvshl #b0000000000001010 #b0000000000000001) n) (ite (bvuge #b0000000000001010 n) #b0000000000000001 _let_1) _let_1)))

;; Init Check: n=0 -> x=1, y=-20, z=1
(push)
(assert (not (and 
    (= (fx #x0000) #x0001) 
    (= (fy #x0000) #xffec)
    (= (fz #x0000) #x0001)
)))
(check-sat)
(pop)

;; Trans Check
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun z_curr () (_ BitVec 16) (fz n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))
(define-fun z_next () (_ BitVec 16) (fz (bvadd n #x0001)))

(define-fun trans_holds () Bool
    (or 
      (bvugt n #x0019) ;; Stop at 25
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next (bvadd y_curr #x0002))
        (= z_next (ite (bvsge y_curr #x0000) (bvmul z_curr #x0002) z_curr)) 
      )
    )
)

(assert (not trans_holds))
;; We restrict n to avoid overflow issues confusing the logic? 
;; Though BV logic should handle overflow identically in function and trans.
(check-sat)
