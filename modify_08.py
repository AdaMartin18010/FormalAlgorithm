import re

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

# 1. Insert higher-order quantifiers after HOL vs FOL comparison
quantifiers_section = """## 高阶量词与类型层级 / Higher-Order Quantifiers and Type Hierarchy

### 二阶量词 / Second-Order Quantifiers

**定义** (二阶量词 / Second-Order Quantifiers)
在二阶逻辑中，量词可直接作用于谓词和函数变量：

- **全称二阶量词**：$\\forall X. \\phi(X)$，表示"对所有一元谓词 $X$，$\\phi(X)$ 成立"；
- **存在二阶量词**：$\\exists X. \\phi(X)$，表示"存在某个一元谓词 $X$，使得 $\\phi(X)$ 成立"。

类似地，对于 $n$ 元关系变量可定义 $\\forall X^{(n)}. \\phi(X^{(n)})$，对于函数变量可定义 $\\forall f. \\phi(f)$。二阶量词的引入使得逻辑系统能够直接表达集合论中的概括原则：

$$\\exists P. \\forall x. P(x) \\leftrightarrow \\phi(x)$$

**定理** (二阶 Peano 算术的范畴性)
二阶 Peano 算术 $PA_2$ 在标准语义下是范畴的（categorical）：任意两个满足 $PA_2$ 的模型都同构。这意味着二阶逻辑能够唯一刻画自然数结构，克服了一阶逻辑由于 Löwenheim-Skolem 定理导致的非范畴性缺陷 [Shapiro1991]。

### 高阶量词层级 / Higher-Order Quantifier Hierarchy

**定义** (简单类型论中的阶 / Order in Simple Type Theory)
在 Church 的简单类型论中，类型按**阶**（order）分层：

- **0 阶**（个体类型）：$\\iota$
- **1 阶**（命题与个体上的关系）：$o$, $\\iota \\rightarrow o$, $\\iota \\rightarrow \\iota$
- **2 阶**（1 阶上的关系与函数）：$(\\iota \\rightarrow o) \\rightarrow o$
- **$n+1$ 阶**：$n$ 阶类型上的关系与函数

一个公式所属的逻辑**阶数**由其中量词所约束变量的最高阶决定。一阶逻辑只允许 0 阶变量上的量化；二阶逻辑允许最高到 1 阶的量化；一般地，$n$ 阶逻辑允许最高到 $n-1$ 阶的量化。

**定义** (累积层次 / Cumulative Hierarchy)
类似于集合论中的 von Neumann 累积层次 $V_\\alpha$，高阶逻辑的语义也可以按累积层次组织：

$$D_0 \\subseteq D_1 \\subseteq D_2 \\subseteq \\cdots$$

其中 $D_0$ 是个体域，$D_{n+1}$ 包含 $D_n$ 上的所有关系和函数。标准语义对应于取 $D_\\infty = \\bigcup_n D_n$ 作为整个类型框架的解释域。这一结构与集合论中的类型论基础（如 $ZF$ 的集合分层）具有深刻的对应关系 [Andrews2002]。

**注记** / **Remark**：高阶量词层级与集合论的对应揭示了高阶逻辑的集合论本质——从某种意义上说，$n$ 阶逻辑就是在不使用显式集合论语言的情况下，表达关于 $V_{n+1}$ 的数学真理。

"""

content = content.replace(
    "**关键洞察**：HOL 将逻辑与集合论的边界推向更内层——在 FOL 中，我们只能谈论个体；在 HOL 中，我们可以直接谈论性质、函数、性质的性质，从而使数学归纳、良基性、有限性等概念能够用单一公式刻画 [Andrews2002]。",
    "**关键洞察**：HOL 将逻辑与集合论的边界推向更内层——在 FOL 中，我们只能谈论个体；在 HOL 中，我们可以直接谈论性质、函数、性质的性质，从而使数学归纳、良基性、有限性等概念能够用单一公式刻画 [Andrews2002]。\n\n" + quantifiers_section
)

# 2. Insert higher-order inductive definitions before Application Domains
inductive_section = """## 高阶归纳定义 / Higher-Order Inductive Definitions

### 归纳谓词与最小不动点 / Inductive Predicates and Least Fixed Points

**定义** (高阶归纳谓词 / Higher-Order Inductive Predicate)
给定一个高阶算子 $\\Phi: (D \\rightarrow \\{\\top, \\bot\\}) \\rightarrow (D \\rightarrow \\{\\top, \\bot\\})$，若 $\\Phi$ 在集合包含序下单调，则根据 Tarski 不动点定理，$\\Phi$ 存在唯一的最小不动点 $\\mu \\Phi$ 和最大的最大不动点 $\\nu \\Phi$：

$$\\mu \\Phi = \\bigvee_{\\alpha} \\Phi^\\alpha(\\emptyset), \\quad \\nu \\Phi = \\bigwedge_{\\alpha} \\Phi^\\alpha(D)$$

最小不动点 $\\mu \\Phi$ 对应**归纳定义**的谓词：例如，自然数的"偶数"谓词可定义为最小不动点：

$$\\text{Even} = \\mu E. \\{0\\} \\cup \\{n+2 \\mid n \\in E\\}$$

在高阶逻辑中，这类不动点定义被广泛用于形式化递归数据类型（如列表、树）和可达性关系 [LambekScott1986]。

### 余归纳与无限数据结构 / Coinduction and Infinite Data Structures

**定义** (余归纳 / Coinduction)
余归纳是通过**最大不动点** $\\nu \\Phi$ 定义无限对象的方法。与归纳关注"有限构造"不同，余归纳关注"观察等价"：两个对象相等当且仅当它们在所有可观察行为上无法区分。

**示例** (无限流 / Infinite Streams)
无限比特流 $\\text{Stream} = \\{0,1\\}^\\omega$ 可定义为最大不动点：

$$\\text{Stream} = \\nu S. \\{0,1\\} \\times S$$

在 Coq 证明助手中，余归纳类型 `CoInductive` 允许直接构造和推理此类无限数据结构。例如，Thue-Morse 序列可以作为一个余归纳对象定义，并通过 coinductive proof 证明其周期性性质。

**归纳 vs 余归纳的对比**：

| 特征 | 归纳 (Induction) | 余归纳 (Coinduction) |
| :--- | :--- | :--- |
| 不动点类型 | 最小不动点 $\\mu$ | 最大不动点 $\\nu$ |
| 证明原则 | 结构归纳法 | 互模拟（bisimulation） |
| 典型数据类型 | 自然数、有限列表、有限树 | 无限流、进程、延迟计算 |
| 构造限制 | 要求良基性（无无限下降链） | 允许无限展开 |
| 使用场景 | 终止性证明、语法分析 | 并发系统、惰性语言语义 |

### 高阶归纳类型 / Higher-Inductive Types

**定义** (高阶归纳类型 / Higher-Inductive Types, HITs)
高阶归纳类型是归纳类型在高阶逻辑/同伦类型论中的扩展，允许在类型定义中同时引入**点构造子**（point constructors）和**路径构造子**（path constructors）。路径构造子定义了类型中元素之间的相等关系。

**在 Coq 与 Lean 中的实现**：
- **Coq** 通过 `Inductive` 和 `CoInductive` 命令支持（严格）归纳和余归纳类型。对于高阶归纳类型，需要借助 `Equations` 插件或 HoTT 库扩展。
- **Lean** 通过 `inductive` 命令原生支持带递归的归纳类型。Lean 4 进一步通过 `partial` 和 `mutual` 归纳支持更复杂的相互递归定义。对于真正的 HITs（如同伦圆 $S^1$），Lean 的 HoTT 实现（如 `lean-hott` 库）提供了实验性支持。

**示例** (同伦圆 $S^1$)
同伦圆是高阶归纳类型的经典例子，其定义包含一个基点 `base` 和一个自回路 `loop`：

```lean
inductive S1 : Type where
  | base : S1
  | loop : base = base
```

这里 `loop : base = base` 是一个路径构造子，断言 `base` 与自身相等，但这个相等不是平凡的——它生成了圆的基本群 $\\pi_1(S^1) \\cong \\mathbb{Z}$ [Jacobs1999]。

**注记** / **Remark**：高阶归纳类型将逻辑中的相等关系从"命题"提升为"构造对象"，深刻改变了数学基础的形式化方式。它们是现代证明助手处理代数拓扑、范畴论语义等高级主题的关键工具。

"""

content = content.replace(
    "## 应用领域 / Application Domains",
    inductive_section + "## 应用领域 / Application Domains"
)

# 3. Add categorical semantics section before Application Domains
cat_semantics = """### 范畴论语义 / Categorical Semantics

**定义** (Topos 与高阶逻辑 / Topos and Higher-Order Logic)
一个 **Topos** 是一个具有幂对象（power object）的笛卡尔闭范畴。Lambek 和 Scott 证明了：高阶直觉逻辑的内部语言（internal language）恰好对应于一个 Topos 的逻辑结构 [LambekScott1986]。

在 Topos 语义中：
- 类型 $\\tau$ 对应于 Topos 中的对象 $[[\\tau]]$；
- 项 $t: \\tau$ 对应于从终对象到 $[[\\tau]]$ 的态射；
- 命题 $\\phi$ 对应于子对象分类器 $\\Omega$ 的态射；
- 量词 $\\forall$ 和 $\\exists$ 对应于子对象分类器的伴随运算。

**定义** (高阶逻辑的内部语言 / Internal Language of HOL)
每个 Topos $\\mathcal{E}$ 都携带一个高阶逻辑系统，称为其**内部语言**。在这个语言中，我们可以像书写集合论公式一样书写范畴论语句，且所有推导在 $\\mathcal{E}$ 中都有效当且仅当它们在标准高阶逻辑中可证。

这一对应关系的重要性在于：它为高阶逻辑提供了独立于集合论的语义基础。例如，有效拓扑斯（effective topos）为高阶逻辑提供了可计算性语义，其中"存在"量词对应于可计算存在性（即有见证的构造），这与构造性高阶逻辑（如 Martin-Löf 类型论）的哲学完全一致 [Jacobs1999]。

**定理** (Soundness and Completeness for Categorical Semantics)
高阶逻辑在 Topos 语义下是可靠的（sound）。对于直觉高阶逻辑，其范畴论语义还具有某种意义上的完备性——这与标准集合论语义下的不完备性形成了有趣的对比 [LambekScott1986]。

"""

# Insert after the type-theoretic semantics section
marker = "> 📚 **概念引用**：关于 **语义理论** 的完整定义，详见 `docs/知识图谱/concept_nodes.yaml` 中 `semantics` 的定义，或参见 `docs/01-基础理论/02-语义理论.md`。"
if marker in content:
    content = content.replace(marker, marker + "\n\n" + cat_semantics)
else:
    # Fallback: insert before Application Domains
    content = content.replace(
        "## 应用领域 / Application Domains",
        cat_semantics + "## 应用领域 / Application Domains"
    )

with open("docs/06-逻辑系统/08-高阶逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("08 modifications done, length:", len(content))
