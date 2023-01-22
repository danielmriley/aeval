(declare-rel inv (Int Int ))
(declare-var i0 Int)
(declare-var i1 Int)
(declare-var range0 Int)
(declare-var range1 Int)

(rule (=> (= range0 20) (inv i0 range0)))

(rule (=> (and
        (inv i0 range0)
        (and (<= 0 i0) (<= i0 range0))
        (= i1 (ite (not (and (= i0 0) (= i0 range0))) (ite (= i0 range0) 0 (+ i0 1)) i0))
        (= range1 (ite (not (and (= i0 0) (= i0 range0))) (ite (= i0 range0) (- range0 1) range0) range0))
        )
    (inv i1 range1)))

; cyclic paths not supported