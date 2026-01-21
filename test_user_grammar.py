
import os

def generate_grammar_experiment():
    # 1. Experiment 1: s_split_01 (The one with 5000)
    # Re-using the constraints from s_split_experiment.sygus
    
    constraints = []
    with open("s_split_experiment.sygus", 'r') as f:
        lines = f.readlines()
        for line in lines:
            if line.strip().startswith("(constraint"):
                constraints.append(line)

    with open("s_split_01_user_grammar.sygus", 'w') as f:
        f.write("(set-logic BV)\n")
        
        for name in ["fx", "fy"]:
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            # Constants pulled from system (s_split_01 has 0, 1, 5000, 10000)
            f.write("    #x0000\n")
            f.write("    #x0001\n")
            f.write("    #x1388\n") # 5000
            f.write("    #x2710\n") # 10000
            
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            # User suggested structure: Boolean rules on Start terms
            f.write("     (bvult Start Start)\n")
            f.write("     (bvuge Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        for c in constraints:
            f.write(c)
        f.write("\n(check-synth)\n")
    
    print("Generated s_split_01_user_grammar.sygus")

    # 2. Experiment 2: s_split_05 (The one with doubling)
    # We need to regenerate the trace data for 05 first.
    
    trace_05_x = []
    trace_05_y = []
    trace_05_z = []
    # logic: x++, y+=2. if old_y >= 0 (starts -20) z*=2 else z=z. 
    x, y, z = 1, -20, 1
    for i in range(25):
        trace_05_x.append(x)
        trace_05_y.append(y)
        trace_05_z.append(z)
        
        old_y = y
        old_z = z
        x = x + 1
        y = y + 2
        if old_y >= 0:
            z = old_z * 2
        else:
            z = old_z
            
    with open("s_split_05_user_grammar.sygus", 'w') as f:
        f.write("(set-logic BV)\n")
        
        state_vars = {"fx": trace_05_x, "fy": trace_05_y, "fz": trace_05_z}
        
        for name in state_vars.keys():
            f.write(f"(synth-fun {name} ((n (_ BitVec 16))) (_ BitVec 16)\n")
            f.write("  ((Start (_ BitVec 16)) (MyBool Bool))\n")
            f.write("  ((Start (_ BitVec 16) (\n")
            f.write("    n\n")
            # Constants from s_split_05 (0, 1, 2)
            f.write("    #x0000\n")
            f.write("    #x0001\n")
            f.write("    #x0002\n")
            f.write("    #x000A\n") # 10 (Derived from -20/2 transition point? Let's check if solver finds it purely from structure)
            
            f.write("    (bvadd Start Start)\n")
            f.write("    (bvsub Start Start)\n")
            f.write("    (bvshl Start Start)\n") # Creating powers of 2
            f.write("    (ite MyBool Start Start)\n")
            f.write("  ))\n")
            f.write("   (MyBool Bool (\n")
            f.write("     (bvult Start Start)\n")
            f.write("     (bvuge Start Start)\n")
            f.write("     (= Start Start)\n")
            f.write("   )))\n")
            f.write(")\n\n")
            
        for i in range(25):
             hex_i = f"#x{i:04x}"
             for name, vals in state_vars.items():
                 val = vals[i]
                 if val < 0: val += 65536
                 hex_val = f"#x{val:04x}"
                 f.write(f"(constraint (= ({name} {hex_i}) {hex_val}))\n")
        
        f.write("\n(check-synth)\n")
        
    print("Generated s_split_05_user_grammar.sygus")

if __name__ == "__main__":
    generate_grammar_experiment()
