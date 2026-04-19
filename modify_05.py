import re

with open("docs/06-逻辑系统/05-多值逻辑理论.md", "r", encoding="utf-8") as f:
    content = f.read()

kleene_insert = """**定义 2.2.5** (Kleene 三值逻辑与部分递归函数 / $K_3$ and Partial Recursive Functions)
Kleene 引入三值逻辑 $K_3$ 的初衷是为**部分递归函数**的谓词提供一个自然的逻辑框架。对于递归可枚举集 $W_e$ 的特征函数：

$$
\\chi_{W_e}(x) = \\begin{cases}
\\mathsf{T} & \\text{if } \\phi_e(x) \\downarrow \\text{（停机）} \\
\\mathsf{F} & \\text{if } \\phi_e(x) \\downarrow \\text{ 且输出为 } 0 \\
\\mathsf{U} & \\text{if } \\phi_e(x) \\uparrow \\text{（不停机）}
\\end{cases}
$$

在此框架下，$K_3$ 的真值表恰好刻画了部分可计算谓词的逻辑行为：当某个子程序不终止时，复合程序的逻辑值保持为"不可判定"($\\mathsf{U}$)，但经典逻辑中的有效推理（如假命题蕴含任何命题）仍然成立 [Kleene1952]。这一设计使得 $K_3$ 成为可计算性理论中处理**部分信息**的标准逻辑工具。

"""

content = content.replace(
    "这恰好符合 SQL 三值逻辑中 UNKNOWN 的处理方式 [Codd1979]。",
    "这恰好符合 SQL 三值逻辑中 UNKNOWN 的处理方式 [Codd1979]。\n\n" + kleene_insert
)

bochar_old = """**定义 2.3.2** (博奇瓦尔合取 / Bochvar Conjunction)
$$
x \\land y = \\begin{cases}
\\min(x, y) & \\text{if } x, y \\in \\{0, 1\\} \\
\\frac{1}{2} & \\text{otherwise}
\\end{cases}
$$

---

## 3. 模糊逻辑 (Fuzzy Logic)"""

bochar_new = """**定义 2.3.2** (博奇瓦尔合取 / Bochvar Conjunction)
$$
x \\land y = \\begin{cases}
\\min(x, y) & \\text{if } x, y \\in \\{0, 1\\} \\
\\frac{1}{2} & \\text{otherwise}
\\end{cases}
$$

**定义 2.3.3** (Bochvar 内在无效性 / Internal Invalidity)
Bochvar 三值逻辑 $B_3$ 的核心特征是其**内在无效性**（internal invalidity）：当任一子公式取值为 $\\mathsf{U}$ 时，整个复合公式的值即为 $\\mathsf{U}$。这与 Kleene $K_3$ 的"强逻辑"形成鲜明对比——在 $K_3$ 中，若一个操作数足以确定整体真值（如 $\\mathsf{F} \\land x$），则结果不必为 $\\mathsf{U}$。

Bochvar 还提出了一套**外逻辑**（external logic），通过引入一元算子 $!$（外部断言）将三值命题映射为二值命题：$!x = \\mathsf{T}$ 当且仅当 $x = \\mathsf{T}$，否则 $!x = \\mathsf{F}$。这使得 $B_3$ 既能处理含无意义成分的陈述，又能在元语言层面恢复经典二值推理。

**示例 2.3.1** (数据库 NULL 值的 Bochvar 语义)
与 Kleene 逻辑不同，Bochvar 的语义更贴近数据库中"毒化传播"（poisoning）的 NULL 处理策略：若查询条件中任一字段为 NULL，则无论其他条件如何，整个 WHERE 子句的结果为 UNKNOWN（即 $\\mathsf{U}$）。例如，在严格的数据完整性检查中，若员工的部门字段缺失，则"部门 = '销售' AND 年薪 > 50000"整体被视为不可判定，从而触发数据补全流程。

---

## 3. 模糊逻辑 (Fuzzy Logic)"""

content = content.replace(bochar_old, bochar_new)

lukas_insert = """
**定义 2.1.6** (从 Ł$_3$ 到模糊逻辑的过渡 / From Ł$_3$ to Fuzzy Logic)
Łukasiewicz 三值逻辑 Ł$_3$ 可视为连续真值区间 $[0,1]$ 上的一个离散采样。当将真值空间从 $\\{0, \\frac{1}{2}, 1\\}$ 推广到整个 $[0,1]$ 区间时，即得到 Łukasiewicz 无限值逻辑 Ł$_\\infty$，也就是**模糊逻辑**的奠基系统之一。在这种过渡中：

- 真值从离散三点变为连续统；
- 合取运算 $x \\land y = \\max(0, x + y - 1)$ 成为 t-范数的原型；
- 蕴含运算 $x \\rightarrow y = \\min(1, 1 - x + y)$ 成为**剩余蕴涵**（residuum）的经典实例。

Zadeh 于 1965 年提出模糊集合论 [Zadeh1965]，将 Łukasiewicz 的连续真值思想与工程应用相结合，开创了现代模糊逻辑体系。Ł$_3$ 中的中间值 $\\frac{1}{2}$ 在模糊逻辑中对应"隶属度为 0.5"，表征命题的不完全真或不完全假。

"""

content = content.replace(
    "**注记** / **Remark**: Ł$_\\infty$ 是 MV-代数（Many-Valued algebra）的逻辑对应物，其代数结构满足交换律、结合律以及关键恒等式 $(x \\rightarrow y) \\rightarrow y = (y \\rightarrow x) \\rightarrow x = x \\lor y$ [Chang1958]。",
    "**注记** / **Remark**: Ł$_\\infty$ 是 MV-代数（Many-Valued algebra）的逻辑对应物，其代数结构满足交换律、结合律以及关键恒等式 $(x \\rightarrow y) \\rightarrow y = (y \\rightarrow x) \\rightarrow x = x \\lor y$ [Chang1958]。" + lukas_insert
)

tconorm_insert = """
**定义 3.2.5** (t-余范数 / Triangular Conorm)
映射 $S: [0,1] \\times [0,1] \\rightarrow [0,1]$ 称为 t-余范数（t-conorm 或 s-norm），若满足结合律、交换律、单调性以及边界条件 $S(x, 0) = x$。t-余范数是 t-范数的对偶运算，对应于逻辑析取。常见的 t-余范数包括 [Klement2000]：

| 名称 | t-余范数 $S(x, y)$ |
| :--- | :--- |
| **Zadeh (Gödel)** | $\\max(x, y)$ |
| **Łukasiewicz** | $\\min(1, x + y)$ |
| **概率和 (Probabilistic Sum)** | $x + y - x \\cdot y$ |

**定义 3.2.6** (模糊蕴含算子 / Fuzzy Implication Operators)
除剩余蕴涵外，模糊逻辑中还常用以下蕴含算子：

| 名称 | 定义 $x \\Rightarrow y$ | 来源 |
| :--- | :--- | :--- |
| **Zadeh** | $\\max(1 - x, y)$ | [Zadeh1965] |
| **Łukasiewicz** | $\\min(1, 1 - x + y)$ | [Lukasiewicz1920] |
| **Gödel** | $\\begin{cases} 1 & x \\le y \\\\ y & x > y \\end{cases}$ | [Hajek1998] |
| **Gaines-Rescher** | $\\begin{cases} 1 & x \\le y \\\\ 0 & x > y \\end{cases}$ | [Hajek1998] |
| **Yager** | $y^x$（当 $x, y > 0$） | [Hajek1998] |

不同的蕴含算子适用于不同的应用场景：Zadeh 蕴含适合近似推理，Gödel 蕴含强调前提必须完全真，而 Łukasiewicz 蕴含在连续变化系统中具有良好的光滑性。

"""

marker = "这三类 t-范数分别对应了三种最重要的模糊逻辑系统：Gödel 逻辑 $\\mathbb{G}$、Łukasiewicz 逻辑 $\\mathbb{L}$ 以及乘积逻辑 $\\mathbb{\\Pi}$，它们构成了基本模糊逻辑 (Basic Fuzzy Logic, BL) 的基石 [Hájek1998]。"
content = content.replace(marker, marker + tconorm_insert)

apps_insert = """
**定义 3.3.3** (模糊控制 / Fuzzy Control)
模糊控制是将模糊逻辑应用于控制系统的方法。典型的 Mamdani 型模糊控制器包含以下步骤：
1. **模糊化**：将精确输入转换为模糊集合的隶属度；
2. **规则求值**：利用 t-范数（通常取 min）计算各规则的激活度；
3. **聚合**：利用 t-余范数（通常取 max）聚合所有规则的输出；
4. **去模糊化**：将模糊输出转换为精确控制量（如重心法）。

**定义 3.3.4** (近似推理 / Approximate Reasoning)
近似推理是模糊逻辑的核心应用之一，其基本模式为广义假言推理（Generalized Modus Ponens, GMP）：
- 大前提：若 $A$ 则 $B$（模糊规则）
- 小前提：$A\'（与 $A$ 近似匹配的输入）
- 结论：$B\'（通过合成运算得到的近似输出）

其数学形式为 $B\'(y) = \\sup_{x \\in X} T(A\'(x), I(A(x), B(y)))$，其中 $T$ 为 t-范数，$I$ 为模糊蕴含算子。Łukasiewicz 蕴含由于其在 $[0,1]$ 上的连续性，常被用于要求平滑过渡的近似推理系统 [Hajek1998]。

**定义 3.3.5** (模糊逻辑在机器学习中的应用 / Fuzzy Logic in Machine Learning)
近年来，模糊逻辑与深度学习的融合催生了**神经模糊系统**（Neuro-Fuzzy Systems）：
- **模糊神经网络**：将神经元激活函数解释为隶属函数，使网络输出具有可解释的语义；
- **可解释 AI（XAI）**：利用模糊规则提取深度网络中的知识，生成"若-则"规则集，提升模型的可解释性；
- **模糊聚类**：如 Fuzzy C-Means (FCM) 算法，通过隶属度实现软划分，广泛应用于图像分割和模式识别 [Zadeh1965]。

"""

content = content.replace(
    "**定义 3.3.2** (模糊推理方法 / Fuzzy Inference Methods)\n\n- 扎德推理法 (Zadeh\'s Method)\n- 马姆达尼推理法 (Mamdani\'s Method)\n- 塔卡吉-苏根推理法 (Takagi-Sugeno Method)",
    "**定义 3.3.2** (模糊推理方法 / Fuzzy Inference Methods)\n\n- 扎德推理法 (Zadeh\'s Method)\n- 马姆达尼推理法 (Mamdani\'s Method)\n- 塔卡吉-苏根推理法 (Takagi-Sugeno Method)" + apps_insert
)

alg_section = """---

## 5. 代数语义 / Algebraic Semantics

### 5.1 MV-代数 / MV-Algebras

**定义 5.1.1** (MV-代数 / MV-Algebra)
一个 MV-代数是一个代数结构 $(A, \\oplus, \\neg, 0)$，满足以下公理 [Chang1958]：

1. $(x \\oplus y) \\oplus z = x \\oplus (y \\oplus z)$（结合律）
2. $x \\oplus y = y \\oplus x$（交换律）
3. $x \\oplus 0 = x$（单位元）
4. $\\neg\\neg x = x$（对合律）
5. $x \\oplus \\neg 0 = \\neg 0$（有界性）
6. $\\neg(\\neg x \\oplus y) \\oplus y = \\neg(\\neg y \\oplus x) \\oplus x$（Łukasiewicz 公理）

其中 $x \\oplus y = \\neg x \\rightarrow y$ 是 Łukasiewicz 的强析取（bounded sum），$\\neg x = x \\rightarrow 0$ 为否定。MV-代数是 Łukasiewicz 无限值逻辑 Ł$_\\infty$ 的**代数语义**对应物：Ł$_\\infty$ 中的公式 tautology 恰好对应于在标准 MV-代数 $[0,1]$ 中恒等于 1 的项。

**定理 5.1.1** (Łukasiewicz 逻辑的代数完备性)
Łukasiewicz 无限值逻辑 Ł$_\\infty$ 关于 MV-代数类是（强）完备的。即：公式 $\\phi$ 在 Ł$_\\infty$ 中可证当且仅当它在每一个 MV-代数中都取值为顶元 [Chang1958]。

### 5.2 BL-代数与基本模糊逻辑 / BL-Algebras and Basic Fuzzy Logic

**定义 5.2.1** (BL-代数 / BL-Algebra)
一个 BL-代数是一个代数结构 $(A, \\land, \\lor, *, \\Rightarrow, 0, 1)$，满足 [Hajek1998]：

1. $(A, \\land, \\lor, 0, 1)$ 是有界格；
2. $(A, *, 1)$ 是交换幺半群；
3. $*$ 与 $\\Rightarrow$ 满足**伴随性质**（adjunction）：$z \\le (x \\Rightarrow y)$ 当且仅当 $z * x \\le y$；
4. **可除性**（divisibility）：$x \\land y = x * (x \\Rightarrow y)$；
5. **预线性**（prelinearity）：$(x \\Rightarrow y) \\lor (y \\Rightarrow x) = 1$。

**定理 5.2.1** (Hájek 完备性定理)
基本模糊逻辑 BL 关于 BL-代数类是完备的。三种主要模糊逻辑系统可由其对应的 BL-代数刻画：

- **Łukasiewicz 逻辑** $\\mathbb{L}$：对应满足 $\\neg\\neg x = x$ 的 MV-代数；
- **Gödel 逻辑** $\\mathbb{G}$：对应满足幂等律 $x * x = x$ 的 Gödel 代数；
- **乘积逻辑** $\\mathbb{\\Pi}$：对应满足特定消去律的乘积代数。

这三类逻辑统称为**模糊逻辑的三大基本系统**，它们的代数语义统一于 BL-代数的框架之下 [Hajek1998]。

**注记** / **Remark**：MV-代数是 BL-代数在满足双重否定律条件下的特例，而 BL-代数本身又是更一般的**剩余格**（residuated lattice）的子类。这一代数层次结构清晰地反映了从 Łukasiewicz 逻辑到更广泛的模糊逻辑家族的语义演进。

"""

content = content.replace(
    "---\n\n## 7. 参考文献 / References",
    alg_section + "\n## 7. 参考文献 / References"
)

with open("docs/06-逻辑系统/05-多值逻辑理论.md", "w", encoding="utf-8") as f:
    f.write(content)

print("05 modifications done, length:", len(content))
