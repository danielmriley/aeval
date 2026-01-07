; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 1

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((i (_ BitVec 16))) (_ BitVec 4) (bvsub ((_ extract 3 0) i) (bvnot (bvshl #b0001 #b0010))))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 16) (_ BitVec 4)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 16)))
    (=> (and (bvule #x0000 i) (bvule i #xffff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
        )
    )
  )
)

(check-sat)
