import re

with open('docs/03-形式化证明/03-构造性证明.md', 'r', encoding='utf-8') as f:
    content = f.read()

# Insert BHK interpretation after 1.4 Content Supplement section (before section 2)
insert_bhk = '''
### 1.5 BHK 解释与构造性语义 / BHK Interpretation

**定义 1.5.1** (Brouwer-Heyting-Kolmogorov 解释 / BHK Interpretation) [1][2]
BHK 解释为直觉主义逻辑中的每个连接词和量词提供了构造性证明的语义：

| 公式 | 其构造性证明是... |
|------|-------------------|
| $A \land B$ | 一个二元组 $(p, q)$，其中 $p$ 是 $A$ 的证明，$q$ 是 $B$ 的证明 |
| $A \lor B$ | 一个变体 $\text{inl}(p)$ 或 $\text{inr}(q)$，其中 $p$ 是 $A$ 的证明或 $q$ 是 $B$ 的证明 |
| $A \rightarrow B$ | 一个构造性函数 $f$，将 $A$ 的任意证明 $p$ 映射为 $B$ 的证明 $f(p)$ |
| $\exists x \in X.\, P(x)$ | 一个二元组 $(a, p)$，其中 $a \in X$ 是见证，$p$ 是 $P(a)$ 的证明 |
| $\forall x \in X.\, P(x)$ | 一个构造性函数 $f$，将每个 $a \in X$ 映射为 $P(a)$ 的证明 $f(a)$ |
| $\neg A$ | 一个构造性函数 $f$，将 $A$ 的任意证明映射为矛盾（即 $f : A \rightarrow \bot$） |

**定理 1.5.1** (BHK 与经典真值表的不可调和性) [1]
在 BHK 解释下，排中律 $A \lor \neg A$ 不具有普遍有效性，因为对于任意命题 $A$，我们无法保证总能够构造出 $A$ 的证明或 $A \rightarrow \bot$ 的证明。

---

'''

marker = '**应用决策建模树**：需程序/项提取 → 用构造性证明（§2）；仅需存在性且接受经典逻辑 → 可用反证法；形式化于 Coq/Agda → 优先构造性（见 08-实现示例）。\n\n---'
content = content.replace(marker, marker + '\n' + insert_bhk)

# Insert realizability after section 5 (before section 6)
insert_real = '''
### 5.4 可实现性理论 / Realizability Theory

**定义 5.4.1** (Kleene 可实现性 / Kleene Realizability) [3]
Kleene 于 1945 年提出的可实现性理论是 BHK 解释的形式化实现。设 $e$ 为一个自然数（可视为部分递归函数的哥德尔编码），$A$ 为算术命题。关系 $e \realizes A$（$e$ 实现 $A$）归纳定义如下：

- $e \realizes t_1 = t_2$ 当且仅当 $t_1 = t_2$ 为真且 $e$ 为任意自然数；
- $e \realizes A \land B$ 当且仅当 $(e)_0 \realizes A$ 且 $(e)_1 \realizes B$；
- $e \realizes A \lor B$ 当且仅当 $(e)_0 = 0$ 且 $(e)_1 \realizes A$，或 $(e)_0 = 1$ 且 $(e)_1 \realizes B$；
- $e \realizes A \rightarrow B$ 当且仅当对于所有 $n$，若 $n \realizes A$，则 $\{e\}(n)$ 有定义且 $\{e\}(n) \realizes B$；
- $e \realizes \exists x.\, A(x)$ 当且仅当 $(e)_1 \realizes A((e)_0)$；
- $e \realizes \forall x.\, A(x)$ 当且仅当对于所有 $n$，$\{e\}(n)$ 有定义且 $\{e\}(n) \realizes A(n)$。

其中 $(e)_i$ 为配对投影函数，$\{e\}(n)$ 为第 $e$ 个部分递归函数在输入 $n$ 下的计算。

**定理 5.4.1** (可实现性 soundness) [3]
若公式 $A$ 在 Heyting 算术（HA）中可证，则存在自然数 $e$ 使得 $e \realizes A$。

**推论 5.4.1** [3]
Heyting 算术具有一致性，且不存在 HA 证明 $0 = 1$。

---

'''

# Find a good insertion point - before section 6
marker2 = '## 6. 构造性证明技术 (Constructive Proof Techniques)'
content = content.replace(marker2, insert_real + marker2)

# Add constructive vs classical analysis after section 5 (before the new realizability or after 5.3)
insert_cmp = '''
### 5.5 构造性分析与经典分析的对比 / Constructive vs Classical Analysis

**定义 5.5.1** (Bishop 构造性分析 / Bishop Constructive Analysis) [4]
Bishop 构造性分析（BISH）是一种中立的构造性数学框架，不预设任何特定的构造性哲学立场（如 Brouwer 直觉主义或 Markov 构造主义）。它要求所有证明都是构造性的，但接受任何能够提供构造性内容的公理。

**定理 5.5.1** (Bolzano-Weierstrass 的构造性限制) [4]
在 BISH 中，有界无限点集不一定存在聚点。经典 Bolzano-Weierstrass 定理依赖于排中律来构造聚点，因此不能无条件地纳入构造性分析。

**对比表：构造性 vs 经典分析**

| 概念 | 经典分析 | 构造性分析 (BISH) |
|------|----------|-------------------|
| 实数相等 | $x = y \lor x \neq y$ 普遍有效 | 一般不可判定 |
| 连续函数 | 点态连续 | 一致连续（构造性可证更强） |
| 单调收敛 | 单调有界数列必收敛 | 需额外可计算性条件 |
| 中值定理 | 对连续函数总成立 | 需避免函数在根附近触及零 |
| 紧致性 | Heine-Borel 定理 | 完全有界 + 一致连续 |

**代码示例：构造性实数的逼近表示**

```python
from fractions import Fraction
from typing import Callable

# 构造性实数：一个产生快速收敛有理数序列的函数
ConstructiveReal = Callable[[int], Fraction]

def make_sqrt_2() -> ConstructiveReal:
    """构造 sqrt(2) 的近似序列（巴比伦方法）"""
    def approx(n: int) -> Fraction:
        x = Fraction(1)
        for _ in range(n + 1):
            x = (x + Fraction(2) / x) / 2
        return x
    return approx

def real_eq(a: ConstructiveReal, b: ConstructiveReal, precision: int) -> bool:
    """在指定精度下判断两个构造性实数是否接近"""
    return abs(a(precision) - b(precision)) < Fraction(1, 10 ** precision)

sqrt2 = make_sqrt_2()
print(f"sqrt(2) ≈ {sqrt2(5)} (误差 < 10^-5)")
```

上述 Python 代码展示了构造性分析的核心思想：实数不是静态对象，而是可计算的逼近过程。两个实数「相等」的判定只能在有限精度下进行，这与经典分析中实数相等的绝对性形成鲜明对比 [4]。

---

'''

marker3 = '## 5. 构造性数学 (Constructive Mathematics)'
end_marker = '## 6. 构造性证明技术'
# Insert before section 6 but after the realizability we already inserted
# Actually insert before the realizability section
real_marker = "### 5.4 可实现性理论 / Realizability Theory"
content = content.replace(real_marker, insert_cmp + real_marker)

with open('docs/03-形式化证明/03-构造性证明.md', 'w', encoding='utf-8') as f:
    f.write(content)
