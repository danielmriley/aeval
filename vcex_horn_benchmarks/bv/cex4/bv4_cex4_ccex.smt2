; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 1

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((n (_ BitVec 8))) (_ BitVec 4) (let ((_let_1 ((_ extract 3 0) n))) (bvadd _let_1 _let_1)))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 8) (_ BitVec 4)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 8)))
    (=> (and (bvule #x00 i) (bvule i #x07))
        (and
          (= (select trace_0 i) (var_0_at_i i))
        )
    )
  )
)

(check-sat)
