import sys
import os

def generate_smt2(n, bits=16):
    const1 = 2 * n
    const2 = 4 * n
    template = f"""(declare-rel inv ((_ BitVec {bits}) (_ BitVec {bits})))
(declare-var x0 (_ BitVec {bits}))
(declare-var x1 (_ BitVec {bits}))
(declare-var y0 (_ BitVec {bits}))
(declare-var y1 (_ BitVec {bits}))
(declare-rel fail ())
(rule (=> (and (= x0 (_ bv0 {bits})) (= y0 (_ bv{const1} {bits}))) (inv x0 y0)))
(rule (=> (and (inv x0 y0) (= x1 (bvadd x0 (_ bv1 {bits}))) (= y1 (ite (bvsge x0 (_ bv{const1} {bits})) (bvadd y0 (_ bv1 {bits})) y0))) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (= x0 (_ bv{const2} {bits})) (= y0 x0)) fail))
(query fail)
"""
    return template

if __name__ == "__main__":
    n_values = [2000, 5000]
    # Use absolute path or relative to project root
    out_dir = "bench_horn_split_cex_bv/s_split_01_gen"
    
    if not os.path.exists(out_dir):
        os.makedirs(out_dir)
        
    for n in n_values:
        # Check for potential overflow if we want to be safe, though 5000 is safe for 16-bit
        # 4 * 5000 = 20000 < 65536
        content = generate_smt2(n, bits=16)
        filepath = os.path.join(out_dir, f"s_split_01_n{n}.smt2")
        print(f"Generating {filepath}")
        with open(filepath, "w") as f:
            f.write(content)
