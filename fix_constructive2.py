with open('docs/03-形式化证明/03-构造性证明.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Fix BHK table
content = content.replace('{inl}', r'$\text{inl}')
content = content.replace('{inr}', r'$\text{inr}')
content = content.replace('eg A$', r'\neg A$')
content = content.replace('ightarrow ', r'\rightarrow ')
content = content.replace(' bot$', r' \bot$')
content = content.replace('A 不具有', r'A$ 不具有')

# Fix realizability section - these are trickier because newlines were inserted
# The pattern \r in Python triple quotes became carriage return
# Let's replace the whole broken BHK theorem text
old_bhk = '''在 BHK 解释下，排中律  \\lor 
eg A$ 不具有普遍有效性，因为对于任意命题 $，我们无法保证总能够构造出 $ 的证明或  \\rightarrow \\bot$ 的证明。'''
content = content.replace(old_bhk, '在 BHK 解释下，排中律  \\lor \\neg A$ 不具有普遍有效性，因为对于任意命题 $，我们无法保证总能够构造出 $ 的证明或  \\rightarrow \\bot$ 的证明。')

# Fix realizability - replace broken lines
content = content.replace('e ealizes A', r'e \realizes A')
content = content.replace('e ealizes t', r'e \realizes t')
content = content.replace('e ealizes A', r'e \realizes A')
content = content.replace('e ealizes A', r'e \realizes A')

# Better: find and replace the whole broken realizability section with correct one
# First find where it starts
start_idx = content.find('**定义 5.4.1** (Kleene 可实现性')
end_idx = content.find('---', start_idx + 200)
if start_idx != -1 and end_idx != -1:
    new_real = r'''**定义 5.4.1** (Kleene 可实现性 / Kleene Realizability) [3]
Kleene 于 1945 年提出的可实现性理论是 BHK 解释的形式化实现。设 $ 为一个自然数（可视为部分递归函数的哥德尔编码），$ 为算术命题。关系  \realizes A$（$ 实现 $）归纳定义如下：

-  \realizes t_1 = t_2$ 当且仅当  = t_2$ 为真且 $ 为任意自然数；
-  \realizes A \land B$ 当且仅当 _0 \realizes A$ 且 _1 \realizes B$；
-  \realizes A \lor B$ 当且仅当 _0 = 0$ 且 _1 \realizes A$，或 _0 = 1$ 且 _1 \realizes B$；
-  \realizes A \rightarrow B$ 当且仅当对于所有 $，若  \realizes A$，则 $\{e\}(n)$ 有定义且 $\{e\}(n) \realizes B$；
-  \realizes \exists x.\, A(x)$ 当且仅当 _1 \realizes A((e)_0)$；
-  \realizes \forall x.\, A(x)$ 当且仅当对于所有 $，$\{e\}(n)$ 有定义且 $\{e\}(n) \realizes A(n)$。

其中 _i$ 为配对投影函数，$\{e\}(n)$ 为第 $ 个部分递归函数在输入 $ 下的计算。

**定理 5.4.1** (可实现性 soundness) [3]
若公式 $ 在 Heyting 算术（HA）中可证，则存在自然数 $ 使得  \realizes A$。

**推论 5.4.1** [3]
Heyting 算术具有一致性，且不存在 HA 证明  = 1$。

'''
    content = content[:start_idx] + new_real + content[end_idx+4:]

with open('docs/03-形式化证明/03-构造性证明.md', 'w', encoding='utf-8') as f:
    f.write(content)
