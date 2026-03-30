; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 1

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((n (_ BitVec 8))) (_ BitVec 4) (bvadd ((_ extract 3 0) n) #b0101))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 8) (_ BitVec 4)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 8)))
    (=> (and (bvule #x00 i) (bvule i #x0a))
        (and
          (= (select trace_0 i) (var_0_at_i i))
        )
    )
  )
)

(check-sat)
