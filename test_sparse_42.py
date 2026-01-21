
import os
from run_more_experiments import generate_sygus_file, to_hex16

def run_s_split_42_sparse():
    # s_split_42 logic
    trace_x = []
    trace_y = []
    trace_z = []
    
    x, y, z = 0, 0, 0
    # Run to 18000 (past 17650 check)
    for i in range(18000):
        # Sparse sampling: keep only every 200th point, AND points near boundaries 1765, 3765
        is_boundary = abs(i - 1765) < 5 or abs(i - 3765) < 5
        if i % 200 == 0 or is_boundary:
             trace_x.append(x)
             trace_y.append(y)
             trace_z.append(z)
        
        # SMT Rules:
        # (= x1 (+ x0 1))
        # (= y1 (ite (>= x0 1765) (+ y0 2) (+ y0 1)))
        # (= z1 (ite (>= y0 5765) (+ z0 3) (+ z0 2)))
        
        next_x = x + 1
        
        if x >= 1765: next_y = y + 2
        else: next_y = y + 1
            
        if y >= 5765: next_z = z + 3
        else: next_z = z + 2
            
        x, y, z = next_x, next_y, next_z

    # Custom writer for sparse constraints
    # Constants: 1765 (#x06E5), 3765 (#x0EB5), 5765 (#x1685), 17650 (#x44F2 is > 16bit? No 17650 < 32767)
    constants = [0, 1, 2, 3, 1765, 3765, 5765, 17650]
    filename = "s_split_42_seeded.sygus"
    
    with open(filename, 'w') as f:
        f.write("(set-logic BV)\n")
        state_vars = ["fx", "fy", "fz"]
        
        for name in state_vars:
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            seen = set()
            for c in constants:
                h = to_hex16(c)
                if h not in seen:
                    f.write(f"    {h}\n")
                    seen.add(h)
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (bvmul Start Start)\n") 
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
             # MBP Guards ONLY
            f.write("     (bvult n #x06e5)\n") # 1765
            f.write("     (and (bvult n #x0eb5) (bvuge n #x06e5))\n") # 1765 <= n < 3765
            f.write("     (bvuge n #x0eb5)\n") # n >= 3765
            f.write("   )))\n")
            f.write(")\n\n")
            
        # Regen trace to write specific constraints
        x, y, z = 0, 0, 0
        for i in range(18000):
            is_boundary = abs(i - 1765) < 5 or abs(i - 3765) < 5
            if i % 200 == 0 or is_boundary:
                # Constrain fx(i) = x, fy(i) = y, fz(i) = z
                hi = to_hex16(i)
                hx = to_hex16(x)
                hy = to_hex16(y)
                hz = to_hex16(z)
                f.write(f"(constraint (= (fx {hi}) {hx}))\n")
                f.write(f"(constraint (= (fy {hi}) {hy}))\n")
                f.write(f"(constraint (= (fz {hi}) {hz}))\n")
            
            # Update
            next_x = x + 1
            if x >= 1765: next_y = y + 2
            else: next_y = y + 1
            
            if y >= 5765: next_z = z + 3
            else: next_z = z + 2
            
            x, y, z = next_x, next_y, next_z
            
        f.write("\n(check-synth)\n")
    print("Generated s_split_42_seeded.sygus")

if __name__ == "__main__":
    run_s_split_42_sparse()
