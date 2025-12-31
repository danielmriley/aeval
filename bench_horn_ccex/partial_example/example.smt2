; x = 0;
; y = 0;
; while(true)
;   x++;
;   y = f(y); // something unrelated to x but safe

(set-logic HORN)
(declare-fun inv ((_ BitVec 8) (_ BitVec 8)) Bool)
(declare-fun f ((_ BitVec 8)) (_ BitVec 8))

; Init: x=0, y=0
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (= x #x00) (= y #x00)) (inv x y))
))

; Trans: x' = x+1, y' = f(y)
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)) (x1 (_ BitVec 8)) (y1 (_ BitVec 8)))
  (=> (and (inv x y)
           (= x1 (bvadd x #x01))
           (= y1 (f y)))
      (inv x1 y1))
))

; Bad: x overflows
(assert (forall ((x (_ BitVec 8)) (y (_ BitVec 8)))
  (=> (and (inv x y) (not (< (+ 1 (bv2int x)) 256))) false)
))

(check-sat)
(exit)
