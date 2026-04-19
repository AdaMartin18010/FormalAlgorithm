with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

extra_lines = '''**注记** / **Remark**：高阶逻辑不仅是数学形式化的理论工具，也是计算机科学中程序验证、类型系统和函数式编程语言的共同基础。从 Church 的 $\\lambda^\\rightarrow$ 到现代的 Lean 4，高阶逻辑始终处于形式化方法的核心位置，其理论与实践的不断演进将持续推动自动化推理和可信计算的发展。

'''

marker = '*本文档提供了高阶逻辑理论的完整形式化框架，包括语法、语义、推导系统及其在数学形式化和程序验证中的应用。*'
content = content.replace(marker, extra_lines + marker)

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("08 final expansion done, length:", len(content))
