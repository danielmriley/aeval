
import os

def update_grammar_with_mbp():
    # MBP guards provided by user:
    # (_FH_0 < 4000)
    # ((_FH_0 < 5000) && (_FH_0 >= 4000))
    # ((_FH_0 < 6000) && (_FH_0 >= 5000))
    # (_FH_0 >= 6000)
    
    # We will translate these into the SyGuS grammar as hardcoded boolean options
    # _FH_0 corresponds to 'n' in our synthesis problem.
    # 4000 = #x0fa0
    # 5000 = #x1388
    # 6000 = #x1770
    
    # Terms:
    term_1 = "(bvult n #x0fa0)"
    term_2 = "(and (bvult n #x1388) (bvuge n #x0fa0))"
    term_3 = "(and (bvult n #x1770) (bvuge n #x1388))"
    term_4 = "(bvuge n #x1770)"
    
    # We will add these to the MyBool production
    
    new_grammar = f"""   (MyBool Bool (
     (bvult Start Start)
     (bvuge Start Start)
     (= Start Start)
     
     ;; Explicit Guards from FreqHorn MBP
     {term_1}
     {term_2}
     {term_3}
     {term_4}
   )))"""

    with open("s_split_48_user.sygus", 'r') as f:
        content = f.read()
    
    # We need to replace the MyBool section. 
    # Since I don't know the EXACT current state (it was edited recently), 
    # I'll regex it or reconstruct the file fully since we have the generator script.
    # Actually, simpler to just re-run the generator script with the new grammar?
    # No, the generator script logic is hardcoded. 
    # Let's read the file line by line and replace the MyBool block.
    
    lines = content.splitlines()
    new_lines = []
    skip = False
    
    for line in lines:
        if "(MyBool Bool (" in line:
            new_lines.append(new_grammar)
            skip = True
        elif skip and ")))" in line:
            # End of block
            skip = False
        elif not skip:
            new_lines.append(line)
            
    with open("s_split_48_mbp.sygus", 'w') as f:
        f.write("\n".join(new_lines))
        
    print("Generated s_split_48_mbp.sygus with explicit MBP guards.")

if __name__ == "__main__":
    update_grammar_with_mbp()
