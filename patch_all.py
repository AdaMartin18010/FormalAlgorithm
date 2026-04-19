import re, os

# ========== 05 ==========
path05 = "docs/06-逻辑系统/05-多值逻辑理论.md"
with open(path05, "r", encoding="utf-8") as f:
    text05 = f.read()

sec23 = """### 2.3 博奇瓦尔三值逻辑 (Bochvar Three-Valued Logic)

**定义 2.3.1** (博奇瓦尔否定 / Bochvar Negation)
$$
\\neg x = \\begin{cases}
1 - x & \\text{if } x \\in \\{0, 1\\} \\\\
\\frac{1}{2} & \\text{if } x = \\frac{1}{2}
\\end{cases}
$$

**定义 2.3.2** (博奇瓦尔合取 / Bochvar Conjunction)
$$
x \\land y = \\begin{cases}
\\min(x, y) & \\text{if } x, y \\in \\{0, 1\\} \\\\
\\frac{1}{2} & \\text{otherwise}
\\end{cases}
$$

**定义 2.3.3** (博奇瓦尔析取 / Bochvar Disjunction)
$$
x \\lor y = \\begin{cases}
\\max(x, y) & \\text{if } x, y \\in \\{0, 1\\} \\\\
\\frac{1}{2} & \\text{otherwise}
\\end{cases}
$$

**定义 2.3.4** (内部无效性 / Internal Nullity)
Bochvar 三值逻辑 $B_3$ 的核心特征在于其对第三值 $\\mathsf{N}$（nullity，内部无效）的处理：一旦复合公式中的任一子公式取值为 $\\mathsf{N}$，则整个公式即取值为 $\\mathsf{N}$。这与 Kleene $K_3$ 的"强"语义不同，$B_3$ 的第三值具有**传染性**（contagious），象征着计算或推理中的"无意义"（meaningless）或"类型错误" [10]。

**定义 2.3.5** (Bochvar 强蕴涵 / Bochvar Implication)
$$
x \\rightarrow_B y = \\begin{cases}
1 & \\text{if } x = 0 \\text{ 或 } y = 1 \\\\
0 & \\text{if } x = 1 \\text{ 且 } y = 0 \\\\
\\frac{1}{2} & \\text{otherwise}
\\end{cases}
$$

**定理 2.3.1** (Bochvar 逻辑与经典逻辑的隔离)
在 $B_3$ 中，任何包含至少一个 $\\mathsf{N}$ 的原子命题的复合命题，其真值必为 $\\mathsf{N}$。因此，$B_3$ 中的有效式（tautologies）恰好是经典二值逻辑中的重言式在 $\\{0,1\\}$ 上的限制。这意味着 $B_3$ 不会改变经典逻辑在"有意义"命题上的推理，但严格隔离了"无意义"命题对推理系统的污染 [10]。

**示例 2.3.1** (SQL NULL 与 Bochvar 语义)
SQL 标准中的三值逻辑（3VL）对 NULL 值的处理与 Bochvar 逻辑高度一致。考虑 SQL 查询：

```sql
SELECT * FROM Employees
WHERE salary > 50000 AND years > 5;
```

若某员工的 `salary` 为 NULL，则 `salary > 50000` 的求值结果为 UNKNOWN。在 SQL 的 3VL 中，该 UNKNOWN 值对整个 `AND` 表达式具有传染性：无论 `years > 5` 为真或假，整个 `WHERE` 子句的结果均为 UNKNOWN，该行不会被选中 [4]。这正是 Bochvar 合取算子的行为。与 Kleene $K_3$ 不同的是，SQL 并未利用"假与任何值合取为假"的强 Kleene 规则，而是将 NULL 视为一种必须严格隔离的"无信息"状态，体现了 Bochvar 式的**内部无效性**思想。

---
"""

pat23 = re.compile(r"### 2\\.3 博奇瓦尔三值逻辑.*?\\n---\\s*\\n(?=## 3\\. 模糊逻辑)", re.DOTALL)
text05 = pat23.sub(lambda m: sec23, text05)

sec34 = """### 3.4 模糊逻辑的应用 (Applications of Fuzzy Logic)

模糊逻辑在工程、决策支持和人工智能领域具有广泛的应用。其核心优势在于能够直接处理语言变量（如"高"、"中等"、"低"）和基于规则的近似推理。

**应用领域 1：模糊控制**
Mamdani 于 1974 年首次将模糊逻辑应用于温度控制器设计 [8]。典型的模糊控制系统包含四个模块：
1. **模糊化**（Fuzzification）：将精确输入转换为模糊集合的隶属度；
2. **规则库**（Rule Base）：以"IF-THEN"形式存储专家经验；
3. **推理机**（Inference Engine）：利用 t-范数和剩余蕴涵计算规则激活度；
4. **去模糊化**（Defuzzification）：将模糊输出转换回精确控制量。

**应用领域 2：决策支持与模式识别**
在 Multi-Criteria Decision Making (MCDM) 中，模糊逻辑被用于处理带有主观不确定性的权重分配。例如，在供应商选择问题中，决策者可以用模糊数（如"约 0.8"）表达偏好，利用模糊加权平均算子聚合多个指标 [2]。

**应用领域 3：图像处理与数据挖掘**
模糊 C-均值（Fuzzy C-Means, FCM）聚类算法利用模糊隶属度实现数据的软划分，广泛应用于医学图像分割、客户细分和异常检测。其核心思想是允许一个数据点以不同程度的隶属度属于多个簇，这正是多值逻辑在数据科学中的直接体现 [2]。

"""

pat34 = re.compile(r"(?=## 4\\. 概率逻辑)")
text05 = pat34.sub(lambda m: sec34 + "\n", text05, count=1)

text05 = text05.replace("## 5. 代数语义 / Algebraic Semantics", "## 7. 代数语义 / Algebraic Semantics")
text05 = text05.replace("## 7. 参考文献 / References", "## 8. 参考文献 / References")
text05 = text05.replace(
    "- [7. 参考文献 / References](#7-参考文献--references)",
    "- [7. 代数语义 / Algebraic Semantics](#7-代数语义--algebraic-semantics)\\n- [8. 参考文献 / References](#8-参考文献--references)"
)

text05 = text05.replace("[Łukasiewicz1920, Łukasiewicz1930]", "[6, 9]")
text05 = text05.replace("[Hájek1998]", "[7]")

body05, _ = text05.split("## 8. 参考文献 / References", 1)
if "[11]" not in body05.split("## 7. 代数语义")[0]:
    body05 = body05.replace("其代数结构满足交换律、结合律以及关键恒等式", "其代数结构满足交换律、结合律以及关键恒等式 [11]", 1)
    body05 = body05.replace("是 Łukasiewicz 无限值逻辑 Ł$_\\infty$ 的**代数语义**对应物", "是 Łukasiewicz 无限值逻辑 Ł$_\\infty$ 的**代数语义**对应物 [11]", 1)

refs05 = """## 8. 参考文献 / References

[1] Chang, C. C. "Algebraic analysis of many-valued logics". Transactions of the American Mathematical Society, 88(2): 467-490, 1958.
[2] Zadeh, L. A. "Fuzzy sets". Information and Control, 8(3): 338-353, 1965.
[3] Kleene, S. C. Introduction to Metamathematics. North-Holland, 1952.
[4] Codd, E. F. "Extending the database relational model to capture more meaning". ACM Transactions on Database Systems, 4(4): 397-434, 1979.
[5] Klement, E. P., Mesiar, R., & Pap, E. Triangular Norms. Kluwer Academic Publishers, 2000.
[6] Łukasiewicz, J. "O logice trójwartościowej". Ruch filozoficzny, 5: 170-171, 1920.
[7] Hájek, P. Metamathematics of Fuzzy Logic. Kluwer Academic Publishers, 1998.
[8] Mamdani, E. H., & Assilian, S. "An experiment in linguistic synthesis with a fuzzy logic controller". International Journal of Man-Machine Studies, 7(1): 1-13, 1975.
[9] Łukasiewicz, J., & Tarski, A. "Untersuchungen über den Aussagenkalkül". Comptes Rendus des Séances de la Société des Sciences et des Lettres de Varsovie, 23: 30-50, 1930.
[10] Bochvar, D. A. "On a three-valued logical calculus and its application to the analysis of the paradoxes of the classical extended functional calculus". History and Philosophy of Logic, 2(1-2): 87-112, 1938.
[11] Cignoli, R., D'Ottaviano, I. M. L., & Mundici, D. Algebraic Foundations of Many-Valued Reasoning. Kluwer Academic Publishers, 2000.

"""

text05 = body05 + refs05
with open(path05, "w", encoding="utf-8") as f:
    f.write(text05)
print("Done 05, lines:", len(text05.splitlines()))

# ========== 08 ==========
path08 = "docs/06-逻辑系统/08-高阶逻辑理论.md"
with open(path08, "r", encoding="utf-8") as f:
    text08 = f.read()

# Replace old keys
text08 = text08.replace("[Gödel1931, Church1936]", "[11, 9]")
text08 = text08.replace("[Gödel1931]", "[11]")
text08 = text08.replace("[Howard1980]", "[8]")
text08 = text08.replace("[Girard1989]", "[10]")
text08 = text08.replace("[Church1936]", "[9]")

body08, _ = text08.split("## 参考文献 / References", 1)
refs08 = """## 参考文献 / References

[1] Shapiro, S. Foundations without Foundationalism: A Case for Second-Order Logic. Oxford University Press, 1991.
[2] Henkin, L. "Completeness in the Theory of Types". The Journal of Symbolic Logic, 15(2): 81-91, 1950.
[3] Andrews, P. B. An Introduction to Mathematical Logic and Type Theory: To Truth Through Proof (2nd ed.). Springer, 2002.
[4] Nipkow, T., Paulson, L. C., & Wenzel, M. Isabelle/HOL: A Proof Assistant for Higher-Order Logic. Springer, 2002.
[5] Church, A. "A Formulation of the Simple Theory of Types". The Journal of Symbolic Logic, 5(2): 56-68, 1940.
[6] Lambek, J., & Scott, P. J. Introduction to Higher-Order Categorical Logic. Cambridge University Press, 1986.
[7] Jacobs, B. Categorical Logic and Type Theory. Elsevier, 1999.
[8] Howard, W. A. "The Formulae-as-Types Notion of Construction". In To H.B. Curry: Essays on Combinatory Logic, Lambda Calculus and Formalism, pp. 479-490. Academic Press, 1980.
[9] Church, A. "A Note on the Entscheidungsproblem". The Journal of Symbolic Logic, 1(1): 40-41, 1936.
[10] Girard, J.-Y., Taylor, P., & Lafont, Y. Proofs and Types. Cambridge University Press, 1989.
[11] Gödel, K. "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I". Monatshefte für Mathematik und Physik, 38: 173-198, 1931.

"""

text08 = body08 + refs08
with open(path08, "w", encoding="utf-8") as f:
    f.write(text08)
print("Done 08, lines:", len(text08.splitlines()))

# ========== 09 ==========
path09 = "docs/06-逻辑系统/09-时序逻辑理论.md"
with open(path09, "r", encoding="utf-8") as f:
    text09 = f.read()

body09, _ = text09.split("## 参考文献 / References", 1)
refs09 = """## 参考文献 / References

[1] Pnueli, A. "The Temporal Logic of Programs". In Proceedings of the 18th Annual Symposium on Foundations of Computer Science (FOCS), pp. 46-57. IEEE, 1977.
[2] Clarke, E. M., Grumberg, O., & Peled, D. A. Model Checking. MIT Press, 1999.
[3] Vardi, M. Y., & Wolper, P. "An Automata-Theoretic Approach to Automatic Program Verification". In Proceedings of the 1st IEEE Symposium on Logic in Computer Science (LICS), pp. 332-344. IEEE, 1986.
[4] Sistla, A. P., & Clarke, E. M. "The Complexity of Propositional Linear Temporal Logics". Journal of the ACM, 32(3): 733-749, 1985.
[5] Clarke, E. M., & Emerson, E. A. "Design and Synthesis of Synchronization Skeletons Using Branching Time Temporal Logic". In Logic of Programs (LNCS 131), pp. 52-71. Springer, 1981.
[6] Emerson, E. A., & Halpern, J. Y. "'Sometimes' and 'Not Never' Revisited: On Branching versus Linear Time Temporal Logic". Journal of the ACM, 33(1): 151-178, 1986.
[7] McMillan, K. L. Symbolic Model Checking. Kluwer Academic Publishers, 1993.
[8] Baier, C., & Katoen, J. P. Principles of Model Checking. MIT Press, 2008.

"""

text09 = body09 + refs09
with open(path09, "w", encoding="utf-8") as f:
    f.write(text09)
print("Done 09, lines:", len(text09.splitlines()))

# ========== 10 Comparison Table ==========
table = """---
title: 6.10 逻辑系统对比表 / Logic Systems Comparison
version: 1.0
status: maintained
last_updated: 2026-04-16
owner: 逻辑系统工作组
---

## 6.10 逻辑系统对比表 / Logic Systems Comparison

### 摘要 / Executive Summary

本表对命题逻辑、一阶逻辑、直觉逻辑、模态逻辑、多值逻辑与时序逻辑在真值结构、排中律、完备性、可判定性及典型应用等维度进行系统对比，为学习者提供快速参照框架。

### 对比表

| 逻辑系统 | 真值集合 | 排中律 (LEM) | 完备性 | 可判定性 | 典型应用 |
| :--- | :--- | :--- | :--- | :--- | :--- |
| **命题逻辑** (Propositional Logic) | $\\{0,1\\}$ | ✅ 成立 | ✅ 完备 | ✅ NP-完全 (SAT) | 数字电路设计、布尔可满足性求解、知识库推理 |
| **一阶逻辑** (First-Order Logic) | $\\{0,1\\}$ | ✅ 成立 | ✅ 完备 (Gödel) | ⚠️ 半可判定 | 数学形式化、数据库查询语言、自动定理证明 |
| **直觉逻辑** (Intuitionistic Logic) | $\\{0,1\\}$ (构造性) | ❌ 不成立 | ✅ Kripke 语义下完备 | ⚠️ 半可判定 | 构造性数学、类型论与程序提取、拓扑语义 |
| **模态逻辑** (Modal Logic) | $\\{0,1\\}$ | ✅ 成立 (经典模态) | ✅ Kripke 框架下完备 | ⚠️ 基本系统可判定；扩展系统各异 | 知识表示与推理、形式化验证、哲学分析 |
| **多值逻辑** (Many-Valued Logic) | $[0,1]$ 或有限值 | ❌ 一般不成立 | ✅ 代数语义下完备 | ⚠️ 有限值可判定；无限值半可判定 | 模糊控制、概率推理、数据库 NULL 处理 |
| **时序逻辑** (Temporal Logic) | $\\{0,1\\}$ (路径/状态) | ✅ 成立 | ✅ 模型检测意义下可靠 | ⚠️ LTL/CTL* 为 PSPACE；CTL 为 P | 程序与硬件验证、协议验证、实时系统规约 |

### 说明

- **真值集合**：经典逻辑采用二值真值；多值逻辑推广为连续或离散的多值结构；时序逻辑的真值依赖于计算路径或状态。
- **排中律 (LEM)**：$A \\lor \\neg A$ 在经典逻辑与模态逻辑中成立，但在直觉逻辑与大多数多值逻辑中被拒绝或弱化。
- **完备性**：指是否存在公理系统使得所有语义有效的公式均可证。命题逻辑、一阶逻辑、直觉逻辑（对 Kripke 语义）、模态逻辑（对 Kripke 框架）以及多值逻辑（对代数语义）均具有相应的完备性定理。
- **可判定性**：命题逻辑的可满足性问题为 NP-完全；一阶逻辑为半可判定（递归可枚举但非递归）；LTL 模型检测为 PSPACE-完全；CTL 模型检测为 P-完全（多项式时间）。
- **典型应用**：各行给出了该逻辑系统在计算机科学与数学中的主要应用场景。

### 交叉引用

- 命题逻辑：参见 `06-逻辑系统/01-命题逻辑.md`
- 一阶逻辑：参见 `06-逻辑系统/02-一阶逻辑.md`
- 直觉逻辑：参见 `06-逻辑系统/03-直觉逻辑.md`
- 模态逻辑：参见 `06-逻辑系统/04-模态逻辑.md`
- 多值逻辑：参见 `06-逻辑系统/05-多值逻辑理论.md`
- 时序逻辑：参见 `06-逻辑系统/09-时序逻辑理论.md`

### 参考文献 / References

[1] Enderton, H. B. A Mathematical Introduction to Logic. Academic Press, 2001.
[2] Blackburn, P., de Rijke, M., & Venema, Y. Modal Logic. Cambridge University Press, 2001.
[3] Troelstra, A. S., & van Dalen, D. Constructivism in Mathematics: An Introduction. North-Holland, 1988.
[4] Hájek, P. Metamathematics of Fuzzy Logic. Kluwer Academic Publishers, 1998.
[5] Baier, C., & Katoen, J. P. Principles of Model Checking. MIT Press, 2008.
"""

with open("docs/06-逻辑系统/10-逻辑系统对比表.md", "w", encoding="utf-8") as f:
    f.write(table)
print("Done 10, lines:", len(table.splitlines()))
