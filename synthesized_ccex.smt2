; CCEX file generated from CVC5 SyGuS synthesis
; Main relation: inv
; Number of state variables: 1

; Synthesized closed-form functions for state evolution
(define-fun var_0_at_i ((i (_ BitVec 32))) (_ BitVec 64) (let ((_let_1 ((_ zero_extend 32) i))) (bvand #b0000000000000000000000000000000000000000000000000000000000000001 (bvlshr (bvsub (bvshl _let_1 #b0000000000000000000000000000000000000000000000000000000000000100) _let_1) #b0000000000000000000000000000000000000000000000000000000000000100))))

; Trace arrays (one per state variable)
(declare-const trace_0 (Array (_ BitVec 32) (_ BitVec 64)))

; Assert that trace arrays follow the synthesized functions
(assert
  (forall ((i (_ BitVec 32)))
    (=> (and (bvule #x00000000 i) (bvule i #xffffffff))
        (and
          (= (select trace_0 i) (var_0_at_i i))
        )
    )
  )
)

(check-sat)
