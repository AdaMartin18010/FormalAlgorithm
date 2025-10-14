# 引用规范标准 / Citation Standard

## 1. 概述 / Overview

本文档定义了形式化算法项目中所有引用的标准化规范，确保学术诚信和可追溯性。

**This document defines standardized citation specifications for all references in the formal algorithm project, ensuring academic integrity and traceability.**

---

## 2. 引用原则 / Citation Principles

### 2.1 核心原则 / Core Principles

1. **完整性 / Completeness**: 所有非原创内容必须标注来源
2. **准确性 / Accuracy**: 引用信息必须准确无误
3. **可追溯性 / Traceability**: 读者应能通过引用找到原始文献
4. **规范性 / Standardization**: 遵循国际学术引用标准

### 2.2 引用时机 / When to Cite

**必须引用的情况 / Must cite:**

- ✓ 直接引用他人观点或表述
- ✓ 使用他人的定理、证明或算法
- ✓ 参考他人的实验结果或数据
- ✓ 基于他人的工作进行扩展

**建议引用的情况 / Recommended to cite:**

- ✓ 介绍某个领域的背景知识
- ✓ 对比不同学者的观点
- ✓ 引导读者深入阅读

**无需引用的情况 / No need to cite:**

- ✗ 公共知识（common knowledge）
- ✗ 基本数学定义（如自然数、实数的定义）
- ✗ 标准符号（如 $\in$, $\forall$, $\exists$）

---

## 3. 引用格式 / Citation Format

### 3.1 文内引用 / In-text Citations

#### 格式1：作者-年份格式（推荐）

```markdown
According to Turing (1936), any computable function can be computed by a Turing machine.
根据图灵（1936）的研究，任何可计算函数都可以由图灵机计算。
```

#### 格式2：编号格式

```markdown
Any computable function can be computed by a Turing machine [1].
任何可计算函数都可以由图灵机计算 [1]。
```

#### 格式3：脚注格式

```markdown
Any computable function can be computed by a Turing machine.¹

¹ Turing, A.M. (1936). "On Computable Numbers..."
```

### 3.2 参考文献列表 / Reference List

#### 期刊论文 / Journal Articles

**格式 / Format:**

```text
Author(s). (Year). "Title". *Journal Name*, Volume(Issue), Page range. DOI
```

**示例 / Example:**

```text
Turing, A.M. (1936). "On Computable Numbers, with an Application to the Entscheidungsproblem". *Proceedings of the London Mathematical Society*, 42(2), 230-265. https://doi.org/10.1112/plms/s2-42.1.230
```

#### 书籍 / Books

**格式 / Format:**

```text
Author(s). (Year). *Book Title* (Edition). Publisher.
```

**示例 / Example:**

```text
Cormen, T.H., Leiserson, C.E., Rivest, R.L., & Stein, C. (2009). *Introduction to Algorithms* (3rd ed.). MIT Press.
```

#### 书籍章节 / Book Chapters

**格式 / Format:**

```text
Author(s). (Year). "Chapter Title". In Editor(s) (Eds.), *Book Title* (pp. Page range). Publisher.
```

**示例 / Example:**

```text
Knuth, D.E. (1997). "Fundamental Algorithms". In *The Art of Computer Programming, Volume 1* (3rd ed., pp. 1-650). Addison-Wesley.
```

#### 会议论文 / Conference Papers

**格式 / Format:**

```text
Author(s). (Year). "Title". In *Conference Name* (pp. Page range). Publisher.
```

**示例 / Example:**

```text
Shor, P.W. (1994). "Algorithms for Quantum Computation: Discrete Logarithms and Factoring". In *Proceedings of the 35th Annual Symposium on Foundations of Computer Science* (pp. 124-134). IEEE.
```

#### 在线资源 / Online Resources

**格式 / Format:**

```text
Author/Organization. (Year). "Title". Retrieved from URL [Accessed: Date]
```

**示例 / Example:**

```text
Wikipedia contributors. (2024). "Algorithm". Retrieved from https://en.wikipedia.org/wiki/Algorithm [Accessed: 2024-12-01]
```

---

## 4. 引用类型 / Citation Types

### 4.1 直接引用 / Direct Quotations

**英文引用 / English:**

```markdown
As Knuth stated: "Premature optimization is the root of all evil" (Knuth, 1974, p. 268).
```

**中文引用 / Chinese:**

```markdown
正如高德纳所言："过早优化是万恶之源"（Knuth, 1974, 第268页）。
```

### 4.2 间接引用（转述）/ Paraphrasing

**示例 / Example:**

```markdown
Turing's work established the theoretical foundation for modern computing (Turing, 1936).
图灵的工作为现代计算奠定了理论基础（Turing, 1936）。
```

### 4.3 多作者引用 / Multiple Authors

**2位作者 / 2 Authors:**

```markdown
(Smith & Jones, 2020)
```

**3-5位作者（首次）/ 3-5 Authors (first time):**

```markdown
(Smith, Jones, Brown, White, & Green, 2020)
```

**3-5位作者（后续）/ 3-5 Authors (subsequent):**

```markdown
(Smith et al., 2020)
```

**6位及以上作者 / 6+ Authors:**

```markdown
(Smith et al., 2020)
```

### 4.4 二次引用 / Secondary Citations

**避免使用 / Avoid if possible**, 优先查找原始文献。

**格式 / Format:**

```markdown
(Original Author, Year, as cited in Secondary Author, Year)
```

**示例 / Example:**

```markdown
(Church, 1936, as cited in Rogers, 1967)
```

---

## 5. 特定内容的引用 / Citations for Specific Content

### 5.1 定理和证明 / Theorems and Proofs

```markdown
**定理 1.1** (哥德尔不完备性定理, Gödel, 1931) 任何包含算术的一致形式化系统都是不完备的。

**Theorem 1.1** (Gödel's Incompleteness Theorem, Gödel, 1931) Any consistent formal system containing arithmetic is incomplete.

**参考文献 / Reference:**
Gödel, K. (1931). "Über formal unentscheidbare Sätze der Principia Mathematica und verwandter Systeme I". *Monatshefte für Mathematik und Physik*, 38(1), 173-198.
```

### 5.2 算法 / Algorithms

```markdown
    **算法 2.1** (归并排序, Knuth, 1998)

    **Algorithm 2.1** (Merge Sort, Knuth, 1998)

    ```rust
    // 基于 Knuth (1998) 的归并排序实现
    // Merge sort implementation based on Knuth (1998)
    ```

    **参考文献 / Reference:**
    Knuth, D.E. (1998). *The Art of Computer Programming, Volume 3: Sorting and Searching* (2nd ed.). Addison-Wesley.
```

### 5.3 代码实现 / Code Implementations

```rust
/// 图灵机模拟器
/// Turing machine simulator
/// 
/// 实现参考 / Implementation reference:
/// - Sipser, M. (2012). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.
/// - Hopcroft, J.E., & Ullman, J.D. (1979). *Introduction to Automata Theory*. Addison-Wesley.
pub struct TuringMachine {
    // ...
}
```

### 5.4 数学符号 / Mathematical Notations

```markdown
**符号说明 / Notation:** $\mathbb{N}$ 表示自然数集（参照 ISO 80000-2:2019）。

**Notation:** $\mathbb{N}$ denotes the set of natural numbers (following ISO 80000-2:2019).
```

---

## 6. 引用管理 / Citation Management

### 6.1 引用数据库 / Citation Database

建议维护一个中央引用数据库（如 `docs/references.bib`）：

```bibtex
@article{turing1936,
  author = {Turing, Alan M.},
  title = {On Computable Numbers, with an Application to the Entscheidungsproblem},
  journal = {Proceedings of the London Mathematical Society},
  year = {1936},
  volume = {42},
  number = {2},
  pages = {230--265},
  doi = {10.1112/plms/s2-42.1.230}
}

@book{cormen2009,
  author = {Cormen, Thomas H. and Leiserson, Charles E. and Rivest, Ronald L. and Stein, Clifford},
  title = {Introduction to Algorithms},
  edition = {3rd},
  year = {2009},
  publisher = {MIT Press},
  address = {Cambridge, MA}
}
```

### 6.2 引用检查清单 / Citation Checklist

- [ ] 每个引用都有完整的书目信息
- [ ] 每个书目条目都在文中被引用
- [ ] 所有URL都可访问
- [ ] DOI（如有）都正确
- [ ] 年份、页码等细节准确
- [ ] 引用格式统一规范

---

## 7. 特殊引用情况 / Special Citation Cases

### 7.1 经典教材 / Classic Textbooks

对于广为人知的经典教材，可以使用简化引用：

```markdown
正如经典算法教材所述（CLRS, 2009），归并排序的时间复杂度为 $O(n \log n)$。

As stated in the classic algorithms textbook (CLRS, 2009), merge sort has a time complexity of $O(n \log n)$.
```

### 7.2 Wikipedia 引用 / Wikipedia Citations

Wikipedia应谨慎使用，建议作为概念介绍的起点，但不应作为主要引用来源：

```markdown
**概念介绍 / Concept Introduction:**
算法是解决问题的有限步骤序列（Wikipedia, 2024）。更严格的定义可参见 Knuth (1997)。

An algorithm is a finite sequence of steps to solve a problem (Wikipedia, 2024). For a more rigorous definition, see Knuth (1997).

**参考文献 / References:**
- Wikipedia contributors. (2024). "Algorithm". Retrieved from https://en.wikipedia.org/wiki/Algorithm [Accessed: 2024-12-01]
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 1* (3rd ed.). Addison-Wesley.
```

### 7.3 标准文档 / Standards Documents

```markdown
**引用格式 / Citation Format:**
ISO/IEC 2382-1:2015. Information technology — Vocabulary — Part 1: Fundamental terms. International Organization for Standardization.

**文内引用 / In-text:**
根据 ISO/IEC 2382-1 (2015) 的定义，算法是...

According to ISO/IEC 2382-1 (2015), an algorithm is...
```

---

## 8. 自动化工具 / Automation Tools

### 8.1 引用检查工具 / Citation Checker Tool

项目应开发自动化工具检查引用完整性（见 `docs/可持续改进执行计划2025-2026.md`）：

```rust
/// 引用检查器 / Citation Checker
/// 
/// 功能 / Features:
/// - 检测文内引用是否有对应的参考文献条目
/// - 检测参考文献条目是否在文中被引用
/// - 验证引用格式的一致性
/// - 检查URL和DOI的有效性
pub struct CitationChecker {
    // Implementation details...
}
```

### 8.2 引用提取工具 / Citation Extraction Tool

```rust
/// 引用提取器 / Citation Extractor
///
/// 功能 / Features:
/// - 从Markdown文档中提取所有引用
/// - 生成引用列表
/// - 检测引用缺失
pub struct CitationExtractor {
    // Implementation details...
}
```

---

## 9. 常见错误 / Common Mistakes

### 9.1 避免的错误 / Mistakes to Avoid

❌ **错误1：缺失引用 / Missing Citations**

```markdown
哥德尔不完备性定理表明任何包含算术的一致形式化系统都是不完备的。
```

✅ **正确做法 / Correct:**

```markdown
哥德尔不完备性定理（Gödel, 1931）表明任何包含算术的一致形式化系统都是不完备的。
```

---

❌ **错误2：引用信息不完整 / Incomplete Citation**

```markdown
Turing, A.M. "On Computable Numbers". 1936.
```

✅ **正确做法 / Correct:**

```markdown
Turing, A.M. (1936). "On Computable Numbers, with an Application to the Entscheidungsproblem". *Proceedings of the London Mathematical Society*, 42(2), 230-265.
```

---

❌ **错误3：过度依赖Wikipedia / Over-reliance on Wikipedia**

```markdown
算法是一系列指令（Wikipedia）。
```

✅ **正确做法 / Correct:**

```markdown
算法是解决特定问题的有限、明确、可执行的指令序列（Knuth, 1997）。对于入门级介绍，也可参考 Wikipedia (2024)。

**参考文献:**
- Knuth, D.E. (1997). *The Art of Computer Programming, Volume 1* (3rd ed.). Addison-Wesley.
- Wikipedia contributors. (2024). "Algorithm". Retrieved from https://en.wikipedia.org/wiki/Algorithm
```

---

## 10. 引用覆盖率目标 / Citation Coverage Goals

### 10.1 阶段性目标 / Phased Goals

根据 `docs/可持续改进执行计划2025-2026.md`：

- **第一阶段（2025年11月-2026年2月）/ Phase 1 (Nov 2025 - Feb 2026)**:
  - 核心定理和算法：100%引用覆盖率
  - 基础概念：80%引用覆盖率

- **第二阶段（2026年3月-2026年8月）/ Phase 2 (Mar 2026 - Aug 2026)**:
  - 所有主要内容：90%引用覆盖率
  - 实现示例：70%引用覆盖率

- **第三阶段（2026年9月-2026年12月）/ Phase 3 (Sep 2026 - Dec 2026)**:
  - 整体项目：95%引用覆盖率

### 10.2 质量指标 / Quality Metrics

- **引用完整性 / Citation Completeness**: 所有引用都有完整信息
- **引用准确性 / Citation Accuracy**: 所有引用信息准确无误
- **引用时效性 / Citation Timeliness**: 优先引用近期研究（过去10年）
- **引用权威性 / Citation Authority**: 优先引用顶级期刊和会议

---

## 11. 更新与维护 / Updates and Maintenance

### 11.1 定期审查 / Regular Review

- **每月 / Monthly**: 检查新增内容的引用情况
- **每季度 / Quarterly**: 全面审查引用完整性
- **每年 / Annually**: 更新引用标准和工具

### 11.2 版本控制 / Version Control

所有引用相关的更改都应通过Git跟踪：

```bash
git commit -m "docs: 添加算法设计理论的引用 / Add citations for algorithm design theory"
```

---

## 12. 参考资源 / Reference Resources

### 12.1 引用风格指南 / Citation Style Guides

- **APA Style**: <https://apastyle.apa.org/>
- **IEEE Style**: <https://ieeeauthorcenter.ieee.org/>
- **ACM Reference Format**: <https://www.acm.org/publications/authors/reference-formatting>
- **Chicago Manual of Style**: <https://www.chicagomanualofstyle.org/>

### 12.2 引用管理工具 / Citation Management Tools

- **Zotero**: <https://www.zotero.org/>
- **Mendeley**: <https://www.mendeley.com/>
- **EndNote**: <https://endnote.com/>
- **BibTeX**: <https://www.bibtex.org/>

---

**最后更新 / Last Updated**: 2025年11月 / November 2025

**版本 / Version**: 1.0
