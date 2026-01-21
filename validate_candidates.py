
import os
import subprocess

def run_cvc5(filename):
    print(f"Running validation on {filename}...")
    try:
        # Added --incremental
        res = subprocess.run(["cvc5", "--lang=smt2", "--incremental", filename], capture_output=True, text=True, timeout=10)
        return res.stdout.strip()
    except Exception as e:
        return str(e)

def validate_01():
    # s_split_01
    # Init: x=0, y=5000
    # Trans: x'=x+1, y' = ite(x>=5000, y+1, y)
    smt = """
(set-logic BV)
(set-option :produce-models true)

(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) n)
(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16) (ite (bvult n #x1388) #x1388 n))

;; Init Check: n=0 imply x=0, y=5000
(push)
(assert (not (and (= (fx #x0000) #x0000) (= (fy #x0000) #x1388))))
(check-sat) 
;; Expect UNSAT (negation is false -> valid)
(pop)

;; Trans Check: Implies (Trans) for all n
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))

;; Trans Logic
(define-fun trans_holds () Bool
    (or 
      (bvugt n #x2715) ;; Stop validating after trace end (approx 10005)
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next (ite (bvsge x_curr #x1388) (bvadd y_curr #x0001) y_curr))
      )
    )
)

(assert (not trans_holds))
(check-sat)
;; Expect UNSAT
"""
    with open("validate_01.smt2", "w") as f:
        f.write(smt)
    return run_cvc5("validate_01.smt2")

def validate_05():
    # s_split_05
    # x=1, y=-20, z=1
    # x'=x+1, y'=y+2, z'=ite(y>=0, z*2, z)
    # y=-20 = 65516 (#xffec)
    # 0 = #x0000
    
    # Synthesized functions
    # fx = n+1 (since simulator started x=1 at n=0)
    # fy = 2*n - 20 ? 
    # Logic in simulator: x=1, y=-20.
    # Solver output: 
    # fx: (bvadd n #x0001) -> Matches x=n+1
    # fy: (bvshl (bvsub n #x000a) #x0001). #x000a=10. (n-10)<<1 = 2(n-10) = 2n-20. Matches.
    # fz: That complex string.
    
    fz_def = "(define-fun fz ((n (_ BitVec 16))) (_ BitVec 16) (let ((_let_1 (bvshl #b0000000000000001 (bvsub n #b0000000000001010)))) (ite (bvuge (bvshl #b0000000000001010 #b0000000000000001) n) (ite (bvuge #b0000000000001010 n) #b0000000000000001 _let_1) _let_1)))"
    
    smt = f"""
(set-logic BV)
(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) (bvadd n #x0001))
(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16) (bvshl (bvsub n #x000a) #x0001))
{fz_def}

;; Init Check: n=0 -> x=1, y=-20, z=1
(push)
(assert (not (and 
    (= (fx #x0000) #x0001) 
    (= (fy #x0000) #xffec)
    (= (fz #x0000) #x0001)
)))
(check-sat)
(pop)

;; Trans Check
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun z_curr () (_ BitVec 16) (fz n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))
(define-fun z_next () (_ BitVec 16) (fz (bvadd n #x0001)))

(define-fun trans_holds () Bool
    (or 
      (bvugt n #x0019) ;; Stop at 25
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next (bvadd y_curr #x0002))
        (= z_next (ite (bvsge y_curr #x0000) (bvmul z_curr #x0002) z_curr)) 
      )
    )
)

(assert (not trans_holds))
;; We restrict n to avoid overflow issues confusing the logic? 
;; Though BV logic should handle overflow identically in function and trans.
(check-sat)
"""
    with open("validate_05.smt2", "w") as f:
        f.write(smt)
    return run_cvc5("validate_05.smt2")

def validate_48():
    # s_split_48
    # Constants
    # 4000 = #x0FA0
    # 5000 = #x1388
    # 6000 = #x1770
    # 12000 = #x2EE0
    # 28000 = #x6D60
    # 10000 = #x2710
    
    # Manually Derived Solution
    # fy structure:
    # if n < 4000: n
    # elif n < 5000: 4n - 12000
    # elif n < 6000: 28000 - 4n
    # else: 10000 - n
    
    fy_def = """
(define-fun fy ((n (_ BitVec 16))) (_ BitVec 16)
  (ite (bvult n #x0FA0)
       n
       (ite (bvult n #x1388)
            (bvsub (bvshl n #x0002) #x2EE0) 
            (ite (bvult n #x1770)
                 (bvsub #x6D60 (bvshl n #x0002))
                 (bvsub #x2710 n)))))
"""
    # fx is just n
    fx_def = "(define-fun fx ((n (_ BitVec 16))) (_ BitVec 16) n)"

    smt = f"""
(set-logic BV)
{fx_def}
{fy_def}

;; Init Check: n=0 -> x=0, y=0
(push)
(assert (not (and 
    (= (fx #x0000) #x0000) 
    (= (fy #x0000) #x0000)
)))
(check-sat)
(pop)

;; Trans Check
(declare-const n (_ BitVec 16))
(define-fun x_curr () (_ BitVec 16) (fx n))
(define-fun y_curr () (_ BitVec 16) (fy n))
(define-fun x_next () (_ BitVec 16) (fx (bvadd n #x0001)))
(define-fun y_next () (_ BitVec 16) (fy (bvadd n #x0001)))

;; Logic from bv16_s_split_48.smt2
;; Note uses bvslt/bvsge (Signed)
(define-fun trans_holds () Bool
    (or
      (bvugt n #x2715) ;; Stop at approx 10005
      (and 
        (= x_next (bvadd x_curr #x0001))
        (= y_next 
             (ite (bvslt x_curr #x1388) ;; < 5000
                (ite (bvsge x_curr #x0FA0) ;; >= 4000
                     (bvadd y_curr #x0004) 
                     (bvadd y_curr #x0001))
                (ite (bvsge x_curr #x1770) ;; >= 6000
                     (bvsub y_curr #x0001)
                     (bvsub y_curr #x0004)))
        )
      )
    )
)

(assert (not trans_holds))
(check-sat)
"""
    with open("validate_48.smt2", "w") as f:
        f.write(smt)
    return run_cvc5("validate_48.smt2")

if __name__ == "__main__":
    print("Validating s_split_01...")
    res01 = validate_01()
    print("Result:", res01.replace("\n", " "))
    
    print("\nValidating s_split_05...")
    res05 = validate_05()
    print("Result:", res05.replace("\n", " "))

    print("\nValidating s_split_48 (Manual Solution)...")
    res48 = validate_48()
    print("Result:", res48.replace("\n", " "))
