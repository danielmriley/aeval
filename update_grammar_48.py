
with open("s_split_48_user.sygus", "r") as f:
    content = f.read()

old_grammar = """   (MyBool Bool (
     (bvult Start Start)
     (bvuge Start Start)
     (= Start Start)
   )))"""

new_grammar = """   (MyBool Bool (
     (bvult Start Start)
     (bvuge Start Start)
     (bvule Start Start)
     (bvugt Start Start)
     (= Start Start)
     (not (= Start Start))
   )))"""

new_content = content.replace(old_grammar, new_grammar)

with open("s_split_48_user.sygus", "w") as f:
    f.write(new_content)

print(f"Replaced {content.count(old_grammar)} occurrences.")
