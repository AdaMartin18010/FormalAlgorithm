#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
统一概念引用 - 补充修复
"""

import re
from pathlib import Path


def kg_link(concept_id: str) -> str:
    return f"[`docs/知识图谱/concept_nodes.yaml`](../../知识图谱/concept_nodes.yaml) 中 `{concept_id}` 的定义"


def make_ref_note(name: str, concept_id: str, doc_link: str) -> str:
    return f"> 📚 **概念引用**：关于 **{name}** 的完整定义，详见 {kg_link(concept_id)}，或参见 {doc_link}。\n\n"


replacements = []

# ========== 1. 图灵机重复定义修复 ==========
path = Path("docs/07-计算模型/08-计算模型等价性理论.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """### 2.1 图灵机（Turing Machine）

**定义**：图灵机是一个七元组 `M = (Q, Σ, Γ, δ, q₀, q_accept, q_reject)`，其中：

- `Q`：有限状态集
- `Σ`：输入字母表
- `Γ`：磁带字母表（`Σ ⊆ Γ`）
- `δ`：转移函数 `δ : Q × Γ → Q × Γ × {L, R}`
- `q₀`：初始状态
- `q_accept`：接受状态
- `q_reject`：拒绝状态

### 2.2 λ演算（Lambda Calculus）"""
    new = make_ref_note("图灵机", "turing_machine", "[`docs/07-计算模型/01-图灵机.md`](../../07-计算模型/01-图灵机.md)") + """> 本节简要回顾图灵机的基本结构。详细形式化定义参见上文链接。

### 2.2 λ演算（Lambda Calculus）"""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "图灵机定义块(修复)"))

# ========== 2. 同伦类型论基础定义修复 ==========
path = Path("docs/10-高级主题/02-同伦类型论的高级应用.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    # 更宽容的匹配：从 "## 2.1 基本概念" 到下一个二级标题
    pattern = re.compile(r"## 2\.1 基本概念 \(Basic Concepts\).*?(?=\n## 2\.2 )", re.DOTALL)
    new_section = make_ref_note("同伦类型论", "homotopy_type_theory", "[`docs/05-类型理论/03-同伦类型论.md`](../../05-类型理论/03-同伦类型论.md)") + """> 同伦类型论的基础概念（定义、历史、应用领域）已在主文档中完整阐述。本节直接进入高级应用。

"""
    m = pattern.search(content)
    if m:
        content = content[: m.start()] + new_section + content[m.end() :]
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "同伦类型论基础定义(修复)"))

# ========== 3. 证明助手基础定义修复 ==========
path = Path("docs/10-高级主题/03-证明助手的实现.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    pattern = re.compile(r"## 3\.1 基本概念 \(Basic Concepts\).*?(?=\n## 3\.2 )", re.DOTALL)
    new_section = make_ref_note("证明助手", "proof_assistant", "[`docs/08-实现示例/04-形式化验证.md`](../../08-实现示例/04-形式化验证.md)") + """> 证明助手的基础概念（定义、历史、应用领域）已在形式化验证文档中完整阐述。本文档聚焦实现细节。

"""
    m = pattern.search(content)
    if m:
        content = content[: m.start()] + new_section + content[m.end() :]
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "证明助手基础定义(修复)"))

# ========== 4. 量子纠缠 - 量子机器学习修复 ==========
path = Path("docs/10-高级主题/05-量子机器学习.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """**定义 1.2.3** (量子纠缠 / Quantum Entanglement)
量子比特之间的非局域关联可以捕获复杂的数据关系。

**Definition 1.2.3** (Quantum Entanglement)
Non-local correlations between quantum bits can capture complex data relationships."""
    new = make_ref_note("量子纠缠", "quantum_entanglement", "[`docs/07-计算模型/05-量子计算模型.md`](../../07-计算模型/05-量子计算模型.md)") + """> 以下讨论直接基于量子纠缠概念展开。完整形式化定义与物理意义详见上文链接。

**定义 1.2.3** (量子纠缠 / Quantum Entanglement)
量子比特之间的非局域关联可以捕获复杂的数据关系。

**Definition 1.2.3** (Quantum Entanglement)
Non-local correlations between quantum bits can capture complex data relationships."""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "量子纠缠定义(修复)"))

# ========== 5. 量子纠缠 - 量子信息论与量子编码修复 ==========
path = Path("docs/10-高级主题/09-量子信息论与量子编码.md")
if path.exists():
    content = path.read_text(encoding="utf-8")
    old = """## 量子纠缠理论 / Quantum Entanglement Theory

### 纠缠定义与基本性质 / Definition and Basic Properties of Entanglement

量子纠缠是量子力学中最深刻的现象之一，是量子信息处理的核心资源。

**定义 4.1** 量子纠缠是指复合量子系统中，子系统之间的非局域关联。
**Definition 4.1** Quantum entanglement refers to the non-local correlations between subsystems in a composite quantum system."""
    new = """## 量子纠缠理论 / Quantum Entanglement Theory

""" + make_ref_note("量子纠缠", "quantum_entanglement", "[`docs/07-计算模型/05-量子计算模型.md`](../../07-计算模型/05-量子计算模型.md)") + """> 量子纠缠的完整形式化定义、纠缠度量与蒸馏理论详见上文链接。本节聚焦量子信息论与编码中的应用。

### 纠缠定义与基本性质 / Definition and Basic Properties of Entanglement

量子纠缠是量子力学中最深刻的现象之一，是量子信息处理的核心资源。

**定义 4.1** 量子纠缠是指复合量子系统中，子系统之间的非局域关联。
**Definition 4.1** Quantum entanglement refers to the non-local correlations between subsystems in a composite quantum system."""
    if old in content:
        content = content.replace(old, new)
        path.write_text(content, encoding="utf-8")
        replacements.append((str(path), "量子纠缠定义(修复2)"))

# ========== 6. BQP类引用修复 ==========
for qpath_str in [
    "docs/10-高级主题/08-量子计算复杂性理论.md",
    "docs/10-高级主题/13-量子计算复杂性理论.md",
]:
    qpath = Path(qpath_str)
    if qpath.exists():
        content = qpath.read_text(encoding="utf-8")
        # 找到 "### BQP类 / BQP Class" 并在其前面添加引用（如果还没有）
        marker = "### BQP类 / BQP Class\n\n**定义 5.1.1** (BQP类 / BQP Class)"
        if marker in content and "📚 **概念引用**：关于 **BQP类**" not in content:
            note = make_ref_note("BQP类", "bqp", "[`docs/04-算法复杂度/04-复杂度类.md`](../../04-算法复杂度/04-复杂度类.md)")
            content = content.replace(marker, note + marker)
            qpath.write_text(content, encoding="utf-8")
            replacements.append((str(qpath), "BQP类引用(修复)"))

# 打印统计
print("=== 概念统一补充修复完成 ===")
for p, desc in replacements:
    print(f"[DONE] {p} -> {desc}")
print(f"\n共处理 {len(replacements)} 处重复定义")
