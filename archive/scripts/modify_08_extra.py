with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

# Add more detail to categorical semantics
extra_cat = """#### 高阶逻辑内部语言的实例

**集合论 Topos (Set)**：在集合范畴中，高阶逻辑的内部语言就是经典的 ZFC 集合论高阶片段。子对象分类器 $\\Omega$ 对应于二元集合 $\\{0,1\\}$，量词对应于通常的全称与存在量词。

**有效 Topos (Eff)**：在有效拓扑斯中，命题是带见证的（realizability）。$\\phi \\land \\psi$ 的见证是一对 $(a, b)$，其中 $a$ 见证 $\\phi$、$b$ 见证 $\\psi$。这使得 Eff 成为构造性高阶逻辑（特别是 Heyting 算术）的标准模型 [Jacobs1999]。

**层 Topos (Sheaf Topos)**：在拓扑空间 $X$ 上的层范畴 $\\text{Sh}(X)$ 中，高阶逻辑的内部语言对应于 $X$ 上局部定义的数学对象。例如，内部实数对应于连续实值函数层，这解释了为什么直觉主义分析中"所有函数都是连续的"在层语义下成立 [LambekScott1986]。

"""

marker1 = "**定理** (Soundness and Completeness for Categorical Semantics)"
content = content.replace(marker1, extra_cat + marker1)

# Add explicit completeness differences section
comp_section = """### 完备性差异的深入分析 / Deep Analysis of Completeness Differences

**定理** (标准语义下的紧致性失效)
高阶逻辑在标准语义下不满足紧致性定理。即：存在高阶公式集 $\\Gamma$，使得 $\\Gamma$ 的每个有限子集都有标准模型，但 $\\Gamma$ 本身没有标准模型。

*证明概要*：考虑公式集 $\\Gamma = \\{ \\exists X. \\forall x. x \\in X \\} \\cup \\{ |D| \\ge n \\mid n \\in \\mathbb{N} \\}$。每个有限子集只需取足够大的有限域即可满足，但整个集合要求存在一个包含所有自然数的全域，这在标准语义下与某些附加约束矛盾。

**Henkin 语义下的完备性构造**
Henkin 完备性的证明与一阶逻辑完全类似，核心步骤为：
1. 将高阶公式扩充为一个极大一致集 $\\Delta$；
2. 构造项模型 $\\mathcal{M}_\\Delta$，其中个体为闭项的等价类；
3. 对函数类型，$D_{\\tau \\rightarrow \\sigma}$ 取为所有在 $\\Delta$ 中可定义的 $\\tau \\rightarrow \\sigma$ 函数的集合；
4. 验证概括原则在此模型中成立。

这一构造的巧妙之处在于：它不需要"所有可能的函数"，只需要"足够多的函数"来满足逻辑可定义性即可 [Henkin1950]。

**哲学意义**：标准语义与 Henkin 语义的选择反映了关于"逻辑必然性"的不同哲学立场。标准语义主张逻辑真理应对所有可能结构成立；Henkin 语义则认为逻辑真理只需对所有"合理"的结构（即可定义的函数宇宙）成立。

"""

marker2 = "### 范畴论语义 / Categorical Semantics"
content = content.replace(marker2, comp_section + marker2)

# Add more to higher-order quantifiers section
extra_quant = """**定义** (高阶量词与集合论的对应 / Correspondence with Set Theory)
在高阶逻辑的标准语义中，$n$ 阶量词 $\\forall X^n. \\phi$ 对应于集合论中对 $V_{n+1}$ 的量化。具体地：
- 一阶量词 $\\forall x$ 对应于对集合 $V_1$（即个体域）中元素的量化；
- 二阶量词 $\\forall X$ 对应于对 $V_2 = \\mathcal{P}(V_1)$ 中子集的量化；
- $n$ 阶量词对应于对 $V_{n+1}$ 的量化。

因此，$n$ 阶逻辑的表达能力大致等同于对 $V_{n+1}$ 的集合论陈述能力。完整的高阶逻辑（允许任意有限阶）在表达能力上等价于 $ZFC$ 的一个片段——具体来说，它对应于没有替换公理模式的类型论集合论 [Shapiro1991]。

"""

marker3 = "**注记** / **Remark**：高阶量词层级与集合论的对应揭示了高阶逻辑的集合论本质——从某种意义上说，$n$ 阶逻辑就是在不使用显式集合论语言的情况下，表达关于 $V_{n+1}$ 的数学真理。"
content = content.replace(marker3, marker3 + "\n\n" + extra_quant)

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("08 extra content added, length:", len(content))
