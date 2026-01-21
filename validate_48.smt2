
(set-logic BV)
(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) n)

(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult n #x0FA0)
       n
       (ite (bvult n #x1388)
            (bvsub (bvshl n #x0002) #x2EE0) 
            (ite (bvult n #x1770)
                 (bvsub #x6D60 (bvshl n #x0002))
                 (bvsub #x2710 n)))))


;; Init Check: n=0 -> x=0, y=0
(push)
(assert (not (and 
    (= (fx #x0000) #x0000) 
    (= (fy #x0000) #x0000)
)))
(check-sat)
(pop)

;; Trans Check
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))

;; Logic from bv16_s_split_48.smt2
;; Note uses bvslt/bvsge (Signed)
(define-fun trans_holds () Bool
    (or
      (bvugt n #x2715) ;; Stop at approx 10005
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next 
             (ite (bvslt x_curr #x1388) ;; < 5000
                (ite (bvsge x_curr #x0FA0) ;; >= 4000
                     (bvadd y_curr #x0004) 
                     (bvadd y_curr #x0001))
                (ite (bvsge x_curr #x1770) ;; >= 6000
                     (bvsub y_curr #x0001)
                     (bvsub y_curr #x0004)))
        )
      )
    )
)

(assert (not trans_holds))
(check-sat)
