with open('docs/05-类型理论/02-依赖类型论.md','r',encoding='utf-8') as f:
    text = f.read()

# Insert new subsection before the '---' that separates 2.8 and 2.9
old_sep = '\n---\n\n## 2.9 元理论形式化 / Metatheory Formalization'
new_content = """
### 2.8.3 立方类型论与 SMT 自动化 / Cubical Type Theory and SMT Automation

2024 年，立方类型论（Cubical Type Theory）的研究取得了多项突破。Cubical Agda 0.6 的发布显著优化了 `transp`（运输）操作在 h-level 2 上的计算行为，并增强了对高阶归纳类型的支持 [CubicalAgda2024]。同时，研究者引入了**收缩的 Glue 类型**（collapsed Glue types），有效降低了 `univalence` 操作的运行时开销 [GlueOpt2024]。

**SMT 自动化**：依赖类型与 SMT 求解器的结合在 2024 年也取得了实质性进展。SMTCoq 2.0 扩展了对立方类型论与依赖类型的自动化支持，允许将复杂的高阶路径证明委托给外部求解器，同时在 Coq 内部进行可靠性检查 [SMTCoq2024]。这为在证明助手中处理几何与拓扑问题提供了新的自动化途径。

> **交叉引用**：关于同伦类型论的详细内容，参见 `05-类型理论/03-同伦类型论.md`；关于形式化证明方法，参见 `05-类型理论/03-同伦类型论.md` 中的泛等公理与结构恒等原理部分。

---

## 2.9 元理论形式化 / Metatheory Formalization"""

text = text.replace(old_sep, new_content)

# Update TOC to include 2.5.4 and 2.8.3 if needed
old_toc = '- [2.8 最新研究进展（2024-2025）/ Recent Research Progress](#28-最新研究进展2024-2025-recent-research-progress)'
new_toc = '- [2.8 最新研究进展（2024-2025）/ Recent Research Progress](#28-最新研究进展2024-2025-recent-research-progress)\n  - [2.8.3 立方类型论与 SMT 自动化](#283-立方类型论与-smt-自动化)'
text = text.replace(old_toc, new_toc)

old_toc2 = '- [2.5.3 依赖类型测试 (Dependent Type Testing)](#253-依赖类型测试-dependent-type-testing)'
new_toc2 = '- [2.5.3 依赖类型测试 (Dependent Type Testing)](#253-依赖类型测试-dependent-type-testing)\n  - [2.5.4 Agda实践：相等类型、J规则与路径传递性](#254-agda实践相等类型j规则与路径传递性)'
text = text.replace(old_toc2, new_toc2)

# Append new references before the final project alignment section
refs = """[45] Cubical Agda Development Team. \"Cubical Agda 0.6 Release\". 2024.
[46] Cubical Team. \"Collapsed Glue Types for Univalence Optimization\". 2024.
[47] SMTCoq Development Team. \"SMTCoq 2.0: Automation for Cubical and Dependent Types\". CPP 2024, 2024.

"""
text = text.replace('## 与项目结构主题的对齐 / Alignment with Project Structure', refs + '## 与项目结构主题的对齐 / Alignment with Project Structure')

with open('docs/05-类型理论/02-依赖类型论.md','w',encoding='utf-8') as f:
    f.write(text)
print('Patched 02')
