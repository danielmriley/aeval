; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 1

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((i (_ BitVec 64))) (_ BitVec 64) i)

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 64) (_ BitVec 64)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 64)))
    (=> (and (bvule #x0000000000000000 i) (bvule i #xffffffffffffffff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
        )
    )
  )
)

(check-sat)
