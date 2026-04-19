# 与 ACM Computing Curricula 2020 (CC2020) 的对标


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

> 本文件将《FormalAlgorithm》项目的内容映射到 **ACM/IEEE Computing Curricula 2020** 的知识领域（Knowledge Areas, KAs），以证明本项目的知识体系与国际计算机科学教育标准的兼容性。

---

## 对标框架说明

ACM CC2020 将计算机科学知识划分为多个 **Knowledge Areas (KAs)**，每个 KA 包含若干 **Knowledge Units (KUs)**。以下仅列出与算法、数据结构、复杂度理论、形式化方法直接相关的 KAs：

- **AL** — Algorithms and Complexity（算法与复杂度）
- **DS** — Discrete Structures（离散结构）
- **PL** — Programming Languages（程序设计语言，涉及类型系统与形式语义）
- **SE** — Software Engineering（软件工程，涉及算法工程化与验证）
- **SF** — Systems Fundamentals（系统基础，涉及缓存、并行等）

---

## AL: Algorithms and Complexity

> **核心知识单元**：本项目的最大覆盖领域。

| CC2020 KU | 描述 | 本项目覆盖情况 | 对应路径 |
|-----------|------|----------------|----------|
| AL/Basic Analysis | 基础算法分析：渐近记号、时间/空间复杂度 | ✅ 完整覆盖 | `docs/04-算法复杂度/` |
| AL/Algorithmic Strategies | 算法策略：分治、DP、贪心、回溯、分支限界 | 📝 文档覆盖，部分缺代码 | `docs/09-算法理论/` |
| AL/Fundamental Data Structures | 基础数据结构：数组、链表、栈、队列、树、图、哈希表 | 🟡 树/图覆盖较好，链表/栈/队列/哈希表缺失 | `docs/09-算法理论/01-算法基础/02-数据结构理论.md` |
| AL/Basic Automata Computability and Complexity | 自动机、可计算性、复杂度类 (P, NP) | 📝 理论覆盖良好 | `docs/07-计算模型/`, `docs/09-算法理论/05-NP完全性/` |
| AL/Advanced Computational Complexity | 高级计算复杂度：交互式证明、近似算法、随机算法 | 📝 有专题文档 | `docs/09-算法理论/06-近似算法.md`, `docs/02-复杂度理论/交互式证明系统.md` |
| AL/Advanced Data Structures and Algorithms | 高级数据结构与算法 | 🟡 部分覆盖（B树、线段树、后缀数组等） | `docs/09-算法理论/01-算法基础/24-高级数据结构.md` |
| AL/Distributed and Parallel Algorithms | 分布式与并行算法 | 📝 有理论文档，缺工程实现 | `docs/09-算法理论/03-优化理论/` |
| AL/Machine Learning | 机器学习算法 | 📝 有专题区 | `docs/10-高级主题/02-机器学习算法/` |

### 关键缺口（相对于 CC2020 AL）

1. **AL/Fundamental Data Structures**：链表、栈、队列、哈希表的实现与文档严重缺失。
2. **AL/Algorithmic Strategies**：部分策略（如分支限界）仅有理论概述，缺少 Python 参考实现。
3. **AL/Distributed and Parallel Algorithms**：多线程归并排序、并行前缀和等经典算法缺失。

---

## DS: Discrete Structures

> **核心知识单元**：形式化证明与数学基础的支撑。

| CC2020 KU | 描述 | 本项目覆盖情况 | 对应路径 |
|-----------|------|----------------|----------|
| DS/Sets, Relations and Functions | 集合、关系、函数 | ✅ 基础理论覆盖 | `docs/01-基础理论/` |
| DS/Basic Logic | 基础逻辑：命题逻辑、谓词逻辑 | ✅ 完整覆盖 | `docs/06-逻辑系统/` |
| DS/Proof Techniques | 证明技术：归纳、反证、构造 | ✅ 完整覆盖 | `docs/03-形式化证明/` |
| DS/Basics of Counting | 计数基础 | 📝 有概率分析涉及 | `docs/01-基础理论/` |
| DS/Graphs and Trees | 图与树 | ✅ 文档与代码均覆盖 | `docs/09-算法理论/01-算法基础/05-图算法理论.md` |
| DS/Discrete Probability | 离散概率 | 📝 有随机算法涉及 | `docs/09-算法理论/01-算法基础/11-随机算法理论.md` |

### 特色对齐

- **DS/Proof Techniques**：本项目不仅涵盖传统数学证明，还建立了 **Lean 4 形式化证明** 示例（`examples/lean_proofs/`），这在本科 CC2020 对标中具有显著差异化优势。
- **DS/Graphs and Trees**：与图算法理论（`docs/09-算法理论/`）深度联动，覆盖了图遍历、MST、SSSP、网络流等完整主题。

---

## PL: Programming Languages

> **核心知识单元**：类型系统与形式语义。

| CC2020 KU | 描述 | 本项目覆盖情况 | 对应路径 |
|-----------|------|----------------|----------|
| PL/Type Systems | 类型系统 | ✅ 深入覆盖 | `docs/05-类型理论/` |
| PL/Formal Semantics | 形式语义 | 📝 有基础文档 | `docs/00-算法规范设计框架/` |
| PL/Functional Programming | 函数式编程 | 📝 有 HoTT 与依赖类型 | `examples/lean_proofs/hott_basics.lean` |

### 特色对齐

- **PL/Type Systems**：`docs/05-类型理论/` 包含了从简单类型 λ 演算、System F 到依赖类型和 HoTT 的完整进阶路径，远超一般本科 CC2020 要求，更适合研究生级别参考。

---

## SE: Software Engineering

> **核心知识单元**：算法工程化、可维护性、验证。

| CC2020 KU | 描述 | 本项目覆盖情况 | 对应路径 |
|-----------|------|----------------|----------|
| SE/Software Design | 软件设计 | 🟡 有算法设计模式涉及 | `docs/10-高级主题/04-算法合成与元编程.md` |
| SE/Software Verification and Validation | 软件验证与确认 | 📝 Lean 4 形式化证明 | `examples/lean_proofs/` |
| SE/Software Evolution | 软件演化 | 📝 有算法演化理论 | `docs/10-高级主题/24-算法演化与遗传编程理论.md` |

---

## SF: Systems Fundamentals

> **核心知识单元**：体系结构对算法的影响。

| CC2020 KU | 描述 | 本项目覆盖情况 | 对应路径 |
|-----------|------|----------------|----------|
| SF/Performance | 性能评估与优化 | 📝 有复杂度与优化理论 | `docs/04-算法复杂度/`, `docs/09-算法理论/03-优化理论/` |
| SF/Parallelism | 并行性 | 📝 有并行算法理论 | `docs/09-算法理论/03-优化理论/02-并行算法理论.md` |

### 关键缺口

- **SF/Resource Allocation and Scheduling**：调度算法（如作业调度、CPU 调度）未建立专题。
- **SF/Performance**：缺少缓存感知算法（Cache-Oblivious Algorithms）、内存层级分析等系统视角内容。

---

## 总结：本项目在 CC2020 框架下的定位

### 强项（超出本科平均水平）

1. **形式化证明与类型理论**：Lean 4 + HoTT 的内容在国际本科课程中罕见。
2. **算法复杂度与计算理论**：从基础渐近分析到交互式证明系统、NP 完全性，覆盖了 CC2020 的 AL 领域大部分高级内容。
3. **图算法与网络流**：文档和代码实现较为完整。

### 弱项（需补齐以完整对齐 CC2020）

1. **基础数据结构实现**：栈、队列、链表、哈希表等“入门”内容反而缺失，这直接影响了 AL/Fundamental Data Structures 的对标。
2. **排序算法完整性**：线性时间排序（计数、基数、桶排序）和顺序统计量的缺失，导致 Sorting 领域对标不完整。
3. **系统视角算法**：缓存感知、并行多线程、调度算法等内容薄弱。

### 下一步行动

- **短期（2-4 周）**：补齐 AL/Fundamental Data Structures 和 AL/Algorithmic Strategies 中的缺失主题（参见 [`missing_topics_redlist.md`](./missing_topics_redlist.md) P0/P1）。
- **中期（1-2 个月）**：扩展 SF/Performance 视角，增加缓存分析与并行算法工程实现。
- **长期**：将本对标文件转化为 **CC2020 学习路径生成器**，自动根据学生目标推荐本项目中的学习章节。

---

## 参考

- ACM/IEEE-CS. *Computing Curricula 2020: Paradigms for Global Computing Education*. 2020.
- Cormen, T. H., et al. *Introduction to Algorithms* (4th ed.). MIT Press. 2022.

---

## 参考文献

- 待补充

---

## 知识导航

- [返回目录](README.md)

