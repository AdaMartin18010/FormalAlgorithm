#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
统一概念引用：在非权威文档中将重复概念定义替换为引用链接
"""

import re
from pathlib import Path

# 权威定义映射
AUTHORITY = {
    "turing_machine": {
        "name": "图灵机",
        "doc": "docs/07-计算模型/01-图灵机.md",
        "link": "[`docs/07-计算模型/01-图灵机.md`](../../07-计算模型/01-图灵机.md)",
    },
    "recursive_function": {
        "name": "递归函数",
        "doc": "docs/02-递归理论/01-递归函数定义.md",
        "link": "[`docs/02-递归理论/01-递归函数定义.md`](../../02-递归理论/01-递归函数定义.md)",
    },
    "bqp": {
        "name": "BQP类",
        "doc": "docs/04-算法复杂度/04-复杂度类.md",
        "link": "[`docs/04-算法复杂度/04-复杂度类.md`](../../04-算法复杂度/04-复杂度类.md)",
    },
    "hott": {
        "name": "同伦类型论",
        "doc": "docs/05-类型理论/03-同伦类型论.md",
        "link": "[`docs/05-类型理论/03-同伦类型论.md`](../../05-类型理论/03-同伦类型论.md)",
    },
    "dp": {
        "name": "动态规划",
        "doc": "docs/09-算法理论/01-算法基础/06-动态规划理论.md",
        "link": "[`docs/09-算法理论/01-算法基础/06-动态规划理论.md`](../../09-算法理论/01-算法基础/06-动态规划理论.md)",
    },
    "quantum_entanglement": {
        "name": "量子纠缠",
        "doc": "docs/07-计算模型/05-量子计算模型.md",
        "link": "[`docs/07-计算模型/05-量子计算模型.md`](../../07-计算模型/05-量子计算模型.md)",
    },
    "type_system": {
        "name": "类型系统",
        "doc": "docs/05-类型理论/04-类型系统.md",
        "link": "[`docs/05-类型理论/04-类型系统.md`](../../05-类型理论/04-类型系统.md)",
    },
    "proof_assistant": {
        "name": "证明助手",
        "doc": "docs/08-实现示例/04-形式化验证.md",
        "link": "[`docs/08-实现示例/04-形式化验证.md`](../../08-实现示例/04-形式化验证.md)",
    },
}


def kg_link(concept_id: str) -> str:
    return f"[`docs/知识图谱/concept_nodes.yaml`](../../知识图谱/concept_nodes.yaml) 中 `{concept_id}` 的定义"


def make_ref_note(name: str, concept_id: str, doc_link: str) -> str:
    return f"> 📚 **概念引用**：关于 **{name}** 的完整定义，详见 {kg_link(concept_id)}，或参见 {doc_link}。\n\n"


replacements = []

# ========== 1. 图灵机重复定义替换 ==========
# 文件: docs/09-算法理论/02-复杂度理论/01-计算复杂度理论.md
# 替换: **定义 1.1.2** 图灵机模型... 到下一个标题前的内容
path = Path("docs/09-算法理论/02-复杂度理论/01-计算复杂度理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """**定义 1.1.2** 图灵机模型是理论计算的标准模型。

**Definition 1.1.2** The Turing Machine model is the standard model for theoretical computation.

**图灵机特征 / Turing Machine Features:**

- 有限状态控制 / Finite state control
- 无限磁带 / Infinite tape
- 读写头可以左右移动 / Read-write head can move left and right

### 1.2 问题分类 / Problem Classification"""
    new = make_ref_note("图灵机", "turing_machine", AUTHORITY["turing_machine"]["link"]) + "### 1.2 问题分类 / Problem Classification"
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "图灵机定义块"))

# 文件: docs/07-计算模型/08-计算模型等价性理论.md
# 替换: 2.1 图灵机定义段落 -> 引用
path = Path("docs/07-计算模型/08-计算模型等价性理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """### 2.1 图灵机（Turing Machine）

**定义**：图灵机是一个七元组 `M = (Q, Σ, Γ, δ, q₀, q_accept, q_reject)`，其中：

- `Q`：有限状态集
- `Σ`：输入字母表
- `Γ`：磁带字母表
- `δ`：转移函数
- `q₀`：初始状态
- `q_accept`：接受状态
- `q_reject`：拒绝状态

**解释与直观**：图灵机是理论计算的标准模型，通过有限状态控制器在无限磁带上读写符号来模拟任何有效计算过程 [Sipser2013, §3.1]。"""
    new = make_ref_note("图灵机", "turing_machine", AUTHORITY["turing_machine"]["link"]) + """> 本节简要回顾图灵机的基本结构。详细形式化定义参见上文链接。

### 2.2 λ演算（Lambda Calculus）"""
    # 这里需要小心，2.2 λ演算紧跟在2.1后面
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "图灵机定义块"))

# ========== 2. 递归函数重复定义替换 ==========
path = Path("docs/07-计算模型/08-计算模型等价性理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """### 2.3 μ递归函数（μ-Recursive Functions）

**定义**：μ递归函数由以下基本函数和操作构成：

- **基本函数**：
  - 零函数：`Z(n) = 0`
  - 后继函数：`S(n) = n + 1`
  - 投影函数：`P_i^k(x₁, ..., x_k) = x_i`
- **操作**：
  - **复合**：`h(x) = f(g₁(x), ..., g_k(x))`
  - **原始递归**：`h(0, x) = f(x)`, `h(n+1, x) = g(h(n, x), n, x)`
  - **最小化**：`h(x) = μn[f(n, x) = 0]`（最小的 n 使得 `f(n, x) = 0`）

### 2.4 RAM 模型（Random Access Machine）"""
    new = make_ref_note("递归函数", "recursive_function", AUTHORITY["recursive_function"]["link"]) + """> 本节简要回顾μ递归函数的构造。详细形式化定义参见上文链接。

### 2.4 RAM 模型（Random Access Machine）"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "递归函数定义块"))

# ========== 3. 动态规划重复定义替换 ==========
path = Path("docs/09-算法理论/01-算法基础/01-算法设计理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 替换从 "### 2.2 动态规划" 到 "**设计范式对比矩阵**" 之前的内容
    old = """### 2.2 动态规划 / Dynamic Programming

**定义 2.2.1** (动态规划) [Cormen 2022, Bellman 1957, Wikipedia Dynamic Programming]
动态规划通过子问题重叠求解，避免重复计算。根据[Bellman 1957]的原始定义，动态规划是解决多阶段决策问题的方法。

**形式化表示 / Formal Representation:**
动态规划通过子问题重叠求解：
Dynamic programming solves problems through overlapping subproblems:
$$T(n) = \\sum_{i=1}^k T(n_i) + O(1)$$

**最优子结构性质 / Optimal Substructure Property:** [Cormen 2022]
问题的最优解包含其子问题的最优解。
The optimal solution to a problem contains the optimal solutions to its subproblems.

**重叠子问题性质 / Overlapping Subproblems Property:** [Cormen 2022]
递归算法反复求解相同的子问题。
Recursive algorithms repeatedly solve the same subproblems.

**Wiki概念对齐 / Wiki Concept Alignment:**"""
    new = make_ref_note("动态规划", "dp", AUTHORITY["dp"]["link"]) + """### 2.2 动态规划 / Dynamic Programming

> 以下保留动态规划的核心特征与范式对比，完整形式化定义参见上文链接。

**Wiki概念对齐 / Wiki Concept Alignment:**"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "动态规划定义块"))

# ========== 4. 同伦类型论重复定义替换 ==========
path = Path("docs/10-高级主题/02-同伦类型论的高级应用.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 找到 "## 2.1 基本概念" 和 "## 2.2 同伦类型论在代数拓扑中的应用" 之间的内容
    pattern = re.compile(
        r"(## 2\.1 基本概念 \(Basic Concepts\)\n)(.*?)(## 2\.2 同伦类型论在代数拓扑中的应用)",
        re.DOTALL,
    )
    new_section = make_ref_note("同伦类型论", "hott", AUTHORITY["hott"]["link"]) + """> 同伦类型论的基础概念（定义、历史、应用领域）已在主文档中完整阐述。本节直接进入高级应用。

## 2.2 同伦类型论在代数拓扑中的应用"""
    m = pattern.search(content)
    if m:
        content = content[: m.start()] + new_section + content[m.end(3) :]
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "同伦类型论基础定义"))

# ========== 5. 证明助手重复定义替换 ==========
path = Path("docs/10-高级主题/03-证明助手的实现.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    pattern = re.compile(
        r"(## 3\.1 基本概念 \(Basic Concepts\)\n)(.*?)(## 3\.2 证明助手的实现架构)",
        re.DOTALL,
    )
    new_section = make_ref_note("证明助手", "proof_assistant", AUTHORITY["proof_assistant"]["link"]) + """> 证明助手的基础概念（定义、历史、应用领域）已在形式化验证文档中完整阐述。本文档聚焦实现细节。

## 3.2 证明助手的实现架构"""
    m = pattern.search(content)
    if m:
        content = content[: m.start()] + new_section + content[m.end(3) :]
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "证明助手基础定义"))

# ========== 6. 量子纠缠重复定义替换 ==========
path = Path("docs/10-高级主题/05-量子机器学习.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """**定义 1.2.3** (量子纠缠 / Quantum Entanglement)

复合量子系统的状态不能分解为单个子系统状态的直积时，称这些子系统处于纠缠态。

**形式化表示 / Formal Representation:**
对于双粒子系统，若存在 $|\psi\\rangle_{AB}$ 使得：
$$|\\psi\\rangle_{AB} \\neq |\\psi\\rangle_A \\otimes |\\psi\\rangle_B$$

则称系统处于纠缠态。"""
    new = make_ref_note("量子纠缠", "quantum_entanglement", AUTHORITY["quantum_entanglement"]["link"]) + """> 量子纠缠的完整形式化定义与物理意义详见上文链接。以下直接使用该概念进行量子机器学习讨论。"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "量子纠缠定义"))

path = Path("docs/10-高级主题/09-量子信息论与量子编码.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """## 量子纠缠理论 / Quantum Entanglement Theory

### 4.1 量子纠缠定义

**定义 4.1** 量子纠缠是指复合量子系统中，子系统之间的非局域关联。

**形式化表示 (Formal Representation):**
对于纯态 $|
psi\\rangle_{AB}$，若无法写成 $|
psi\\rangle_A \\otimes |
psi\\rangle_B$ 的形式，则称该态为纠缠态。"""
    new = """## 量子纠缠理论 / Quantum Entanglement Theory

""" + make_ref_note("量子纠缠", "quantum_entanglement", AUTHORITY["quantum_entanglement"]["link"]) + """> 量子纠缠的完整形式化定义、纠缠度量与蒸馏理论详见上文链接。本节聚焦量子信息论与编码中的应用。"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "量子纠缠定义"))

# ========== 7. BQP类重复定义处理 ==========
for qpath in [
    Path("docs/10-高级主题/08-量子计算复杂性理论.md"),
    Path("docs/10-高级主题/13-量子计算复杂性理论.md"),
]:
    if qpath.exists():
        content = qpath.read_text(encoding="utf-8")
        # 在 "### BQP类" 前面添加引用注释
        old = "### BQP类 / BQP Class\n\n**定义 5.1.1** (BQP类 / BQP Class)"
        new = make_ref_note("BQP类", "bqp", AUTHORITY["bqp"]["link"]) + "### BQP类 / BQP Class\n\n**定义 5.1.1** (BQP类 / BQP Class)"
        if old in content:
            content = content.replace(old, new)
            qpath.write_text(content, encoding="utf-8")
            replacements.append((str(qpath), "BQP类引用"))

path = Path("docs/10-高级主题/18-量子算法复杂度理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = "**定义 / Definition**: BQP是可以在多项式时间内以有界错误概率解决的量子问题类。"
    new = make_ref_note("BQP类", "bqp", AUTHORITY["bqp"]["link"]) + old
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "BQP类引用"))

# ========== 8. 类型系统重复定义处理 ==========
path = Path("docs/06-逻辑系统/08-高阶逻辑理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 该文件中的"类型系统"段落实际上是一个Rust实现代码块，不是概念定义。
    # 但在文件开头附近可能有简要介绍。检查一下。
    old = "### 类型系统 / Type System\n\n```rust\npub struct HigherOrderTypeSystem {"
    new = make_ref_note("类型系统", "type_system", AUTHORITY["type_system"]["link"]) + """### 类型系统 / Type System

> 以下代码展示高阶类型系统的一个Rust实现骨架。关于类型系统的完整理论定义，参见上文链接。

```rust
pub struct HigherOrderTypeSystem {"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "类型系统实现注释"))

# 打印统计
print("=== 概念统一完成 ===")
for p, desc in replacements:
    print(f"[DONE] {p} -> {desc}")
print(f"\n共处理 {len(replacements)} 处重复定义")
