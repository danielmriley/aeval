(set-logic HORN)
(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-var x0 (_ BitVec 16))
(declare-var x1 (_ BitVec 16))
(declare-var y0 (_ BitVec 16))
(declare-var y1 (_ BitVec 16))

(declare-rel fail ())

(rule (=> (and (= x0 #x0000) (= y0 #x1388))
    (inv x0 y0)))

(rule (=> (and
        (inv x0 y0)
        (= x1 (bvadd x0 #x0001))
        (= y1 (ite (bvuge x0 #x1388) (bvadd y0 #x0001) y0)))
    (inv x1 y1)))

(rule (=> (and (inv x0 y0) (= x0 #x2710)
    (= y0 x0)) fail))

(query fail)
