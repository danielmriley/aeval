(declare-rel inv ((_ BitVec 16)))
(declare-var a (_ BitVec 16))
(declare-var a1 (_ BitVec 16))

(declare-rel fail ())

(rule (=> (and (= a #x0000)) (inv a)))

(rule (=> (and 
  (inv a)
  (bvult a #x1000)
  (= a1 (bvadd a #x0001)))
  (inv a1)))

(rule (=> (and (inv a) (bvugt a #x1000)) fail))

(query fail :print-certificate true)


; This should be trivial since BV a starts at 0 and increments until it is #x1000.