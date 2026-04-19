with open('docs/05-类型理论/01-简单类型论.md','r',encoding='utf-8') as f:
    text = f.read()

# Remove the misplaced refs block after the note
old_misplaced = """---

[66] Siek, J. G., & Taha, W. "Gradual Typing for Functional Languages". ACM SIGPLAN Notices, 41(6): 81-92, 2006.
[67] Garcia, R., et al. "Abstracting Gradual Typing for Higher-Order Polymorphism". PLDI 2024, 2024.
[68] Castagna, G., & Lanvin, V. "Gradual Typing with Union and Intersection Types". POPL 2024, 2024.
[69] Wadler, P. "Linear Types can Change the World!". Programming Concepts and Methods, 1990.
[70] Aspinall, D., & Hofmann, M. "Linear Types in Rust: A Formal Account". OOPSLA 2024, 2024.
[71] Matsushita, Y., et al. "Ownership and Linear Types in Systems Programming". PLDI 2024, 2024.

## 与项目结构主题的对齐 / Alignment with Project Structure"""
new_misplaced = "## 与项目结构主题的对齐 / Alignment with Project Structure"
text = text.replace(old_misplaced, new_misplaced)

# Insert the new refs before the Citation Guidelines note
old_note = "**引用规范说明 / Citation Guidelines**:"
new_refs = """[77] Siek, J. G., & Taha, W. "Gradual Typing for Functional Languages". ACM SIGPLAN Notices, 41(6): 81-92, 2006.

[78] Garcia, R., et al. "Abstracting Gradual Typing for Higher-Order Polymorphism". PLDI 2024, 2024.

[79] Castagna, G., & Lanvin, V. "Gradual Typing with Union and Intersection Types". POPL 2024, 2024.

[80] Wadler, P. "Linear Types can Change the World!". Programming Concepts and Methods, 1990.

[81] Aspinall, D., & Hofmann, M. "Linear Types in Rust: A Formal Account". OOPSLA 2024, 2024.

[82] Matsushita, Y., et al. "Ownership and Linear Types in Systems Programming". PLDI 2024, 2024.

**引用规范说明 / Citation Guidelines**:"""
text = text.replace(old_note, new_refs)

# Update the note text to say numeric format
text = text.replace('文内采用 [Key] 格式引用，与参考文献列表对应。', '文内采用 [N] 编号格式引用，与参考文献列表对应。')

with open('docs/05-类型理论/01-简单类型论.md','w',encoding='utf-8') as f:
    f.write(text)
print('Fixed 01 refs')
