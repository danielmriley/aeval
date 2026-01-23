import os

template = """(declare-rel inv ((_ BitVec 16) (_ BitVec 16)))
(declare-var x0 (_ BitVec 16))
(declare-var x1 (_ BitVec 16))
(declare-var y0 (_ BitVec 16))
(declare-var y1 (_ BitVec 16))
(declare-rel fail ())
(rule (=> (and (= x0 (_ bv0 16)) (= y0 (_ bv{bound} 16))) (inv x0 y0)))
(rule (=> (and (inv x0 y0) (= x1 (bvadd x0 (_ bv1 16))) (= y1 (ite (bvsge x0 (_ bv{bound} 16)) (bvadd y0 (_ bv1 16)) y0))) (inv x1 y1)))
(rule (=> (and (inv x0 y0) (= x0 (_ bv{target} 16)) (= y0 x0)) fail))
(query fail)
"""

ns = [25, 50, 100, 200, 500, 1000]
output_dir = "/home/daniel/Projects/aeval/bench_horn_split_cex_bv/s_split_01_gen"

for n in ns:
    bound = 2 * n
    target = 2 * bound
    content = template.format(bound=bound, target=target)
    
    filename = f"s_split_01_n{n}.smt2"
    path = os.path.join(output_dir, filename)
    
    with open(path, "w") as f:
        f.write(content)
    print(f"Created {path}")
