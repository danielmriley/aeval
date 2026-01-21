
import os

def update_sygus_experiment():
    # Load s_split_experiment.sygus
    # We want to replace the hardcoded grammar with the generic one.
    
    # Read the data points from original file to keep them.
    constraints = []
    with open("s_split_experiment.sygus", 'r') as f:
        lines = f.readlines()
        for line in lines:
            if line.strip().startswith("(constraint"):
                constraints.append(line)
                
    # Create new file content
    with open("s_split_experiment_generic.sygus", 'w') as f:
        f.write("(set-logic BV)\n")
        
        # Generic Grammar for fx and fy
        for name in ["fx", "fy"]:
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            f.write("    #x0000\n")
            f.write("    #x0001\n")
            f.write("    #x1388\n") # 5000 (kept as a hint, but we want the logic to find the guard)
            f.write("    #x2710\n") # 10000
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            # Generic comparison with ANY constants from the grammar?
            # Or providing a range of choices
            f.write("     (bvuge n #x1388)\n") # 5000
            f.write("     (bvult n #x1388)\n")
            f.write("     (bvuge n #x0000)\n")
            f.write("     (bvuge n #x000A)\n")
            f.write("     (bvuge n #x0064)\n")
            f.write("     (bvult Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        for c in constraints:
            f.write(c)
            
        f.write("\n(check-synth)\n")
        
    print("Created s_split_experiment_generic.sygus")

if __name__ == "__main__":
    update_sygus_experiment()
