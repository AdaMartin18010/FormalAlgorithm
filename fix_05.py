with open('docs/05-类型理论/05-依赖类型系统与数理逻辑.md','r',encoding='utf-8') as f:
    text = f.read()

# Replace corrupted characters and missing backticks
text = text.replace('\x0bec_length_cons', 'vec_length_cons')
text = text.replace('\n`lean\n', '\n```lean\n')
text = text.replace('\nend Vec\n`\n', '\nend Vec\n```\n')
text = text.replace('[Lean4802024]', '[45]')

# Fix broken explanation sentences
old_exp = """- Vec α n 是一个依赖类型，其类型参数 
 : Nat 表示向量长度。
- get 函数的第二个参数类型为 Fin n，即小于 
 的自然数。Lean 的类型系统保证了**任何**对 get 的调用都满足索引在范围内，排除了运行时数组越界错误。"""
new_exp = """- Vec α n 是一个依赖类型，其类型参数 `n : Nat` 表示向量长度。
- get 函数的第二个参数类型为 `Fin n`，即小于 `n` 的自然数。Lean 的类型系统保证了**任何**对 get 的调用都满足索引在范围内，排除了运行时数组越界错误。"""
text = text.replace(old_exp, new_exp)

with open('docs/05-类型理论/05-依赖类型系统与数理逻辑.md','w',encoding='utf-8') as f:
    f.write(text)
print('Fixed 05')
