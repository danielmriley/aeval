(declare-rel inv ((_ BitVec 16)))
(declare-var a (_ BitVec 16))
(declare-var a1 (_ BitVec 16))

(declare-rel fail ())

(rule (=> (and (= a #x0000)) (inv a)))

(rule (=> (and 
  (inv a)
  (bvult a #xfffe)
  (= a1 (bvadd a #x0001)))
  (inv a1)))

(rule (=> (and (inv a) (bvuge a #xffff)) fail))

(query fail :print-certificate true)

