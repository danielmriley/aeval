
import os
from run_more_experiments import generate_sygus_file, to_hex16

def run_s_split_48_sparse():
    # s_split_48.smt2 logic again
    trace_x = []
    trace_y = []
    
    x, y = 0, 0
    # Run to 10005
    for i in range(10005):
        # Sparse sampling: keep only every 50th point, AND points near boundaries 4000, 5000, 6000
        is_boundary = abs(i - 4000) < 5 or abs(i - 5000) < 5 or abs(i - 6000) < 5
        if i % 50 == 0 or is_boundary:
             trace_x.append(x)
             trace_y.append(y)
             # Note: generate_sygus_file uses 'i' as index.
             # If I pass lists of length K, it generates constraints for n=0..K.
             # My generate_sygus function assumes continuous trace (0..len).
             # I need to modify it or write a custom writer here to constrain specific 'n'.
        
        next_x = x + 1
        if x < 5000:
            if x >= 4000: y = y + 4
            else: y = y + 1
        else:
            if x >= 6000: y = y - 1  # (ite (>= x0 6000) (- y0 1) (- y0 4))
            else: y = y - 4
        x = next_x

    # Custom writer for sparse constraints
    # Added 12000 and 28000 to the constants list
    constants = [0, 1, 4, 4000, 5000, 6000, 10000, 12000, 28000]
    filename = "s_split_48_seeded.sygus"
    
    with open(filename, 'w') as f:
        f.write("(set-logic BV)\n")
        state_vars = ["fx", "fy"]
        
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
            f.write("    (bvmul Start Start)\n") # Using mul as 4 is available
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
             # MBP Guards ONLY
            f.write("     (bvult n #x0fa0)\n")
            f.write("     (and (bvult n #x1388) (bvuge n #x0fa0))\n")
            f.write("     (and (bvult n #x1770) (bvuge n #x1388))\n")
            f.write("     (bvuge n #x1770)\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        # Regen trace to write specific constraints
        x, y = 0, 0
        for i in range(10005):
            is_boundary = abs(i - 4000) < 5 or abs(i - 5000) < 5 or abs(i - 6000) < 5
            # Sparse: every 500th point
            if i % 500 == 0 or is_boundary:
                # Constrain fx(i) = x, fy(i) = y
                hi = to_hex16(i)
                hx = to_hex16(x)
                hy = to_hex16(y)
                f.write(f"(constraint (= (fx {hi}) {hx}))\n")
                f.write(f"(constraint (= (fy {hi}) {hy}))\n")
            
            # Update
            if i < 5000:
                if i >= 4000: y += 4
                else: y += 1
            else:
                if i >= 6000: y -= 1
                else: y -= 4
            x += 1
            
        f.write("\n(check-synth)\n")
    print("Generated s_split_48_sparse.sygus")

if __name__ == "__main__":
    run_s_split_48_sparse()
