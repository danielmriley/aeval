
(set-logic BV)
(set-option :produce-models true)

(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) n)
(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16) (ite (bvult n #x1388) #x1388 n))

;; Init Check: n=0 imply x=0, y=5000
(push)
(assert (not (and (= (fx #x0000) #x0000) (= (fy #x0000) #x1388))))
(check-sat) 
;; Expect UNSAT (negation is false -> valid)
(pop)

;; Trans Check: Implies (Trans) for all n
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))

;; Trans Logic
(define-fun trans_holds () Bool
    (or 
      (bvugt n #x2715) ;; Stop validating after trace end (approx 10005)
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next (ite (bvsge x_curr #x1388) (bvadd y_curr #x0001) y_curr))
      )
    )
)

(assert (not trans_holds))
(check-sat)
;; Expect UNSAT
