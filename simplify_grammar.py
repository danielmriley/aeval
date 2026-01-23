
with open('test_simplified.sygus', 'r') as f:
    text = f.read()

old_text = """  (MyBool Bool (
    (and (= Start (bvadd Start #x0001)) (= Start Start) (bvult Start #x0190))
    (and (bvuge Start #x0190) (= Start (bvadd Start #x0001)) (= Start (bvadd Start #x0001)))
    (bvult Start Start)
    (bvuge Start Start)
    (= Start Start)
  ))))"""

new_text = """  (MyBool Bool (
    (bvuge Start #x0190)
    (bvult Start #x0190)
    (bvult Start Start)
    (= Start Start)
  ))))"""

# Normalize line endings/spacing if needed, but here we assume exact match from read_file
# Actually, let's use replace
new_content = text.replace(old_text, new_text)

if new_content == text:
    print("No replacement made!")
else:
    print("Replacement success!")

with open('test_simplified.sygus', 'w') as f:
    f.write(new_content)
