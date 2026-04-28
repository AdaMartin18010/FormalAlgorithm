---
title: MIT 课程体系对齐
version: 1.0
last_updated: 2026-04-19
---

# MIT 课程体系对齐文档

> **对齐日期**: 2026-04-15
> **来源**: MIT OpenCourseWare (ocw.mit.edu)、MIT Course Catalog (student.mit.edu)

本文档将 MIT 算法相关课程体系与项目 `docs/` 和 `examples/` 进行系统对标，识别覆盖缺口并引入前沿内容。

---

## 一、MIT 核心算法课程阶梯

| 课程编号 | 课程名称 | 级别 | 项目覆盖状态 | 核心差距 |
|---------|---------|------|------------|---------|
| **6.0001** | Introduction to Computer Science and Programming in Python | 入门 | ⚠️ | Python 实现覆盖稀疏（仅 ~15 模块） |
| **6.006** | Introduction to Algorithms | 本科核心 | ✅ | 大部分主题已覆盖（排序、图、DP、数据结构） |
| **6.046J** | Design and Analysis of Algorithms | 本科进阶 | ⚠️ | 近似算法、随机算法、摊还分析、高级数据结构有文档但代码稀疏 |
| **6.122** | Advanced Data Structures and Algorithms | 本科高阶 | ⚠️ | 部分高级数据结构（vEB、持久化线段树）已覆盖 |
| **6.506** | Algorithm Engineering | 研究生 | ❌ | **完全缺失**：cache-efficient、external-memory、parallel、write-efficient 算法 |
| **6.890** | Learning-Augmented Algorithms | 研究生 | ❌ | **完全缺失**：ML 增强的经典算法 |
| **6.889** | Sublinear Time Algorithms | 研究生 | ❌ | **完全缺失**：property testing、streaming、sketching |
| **6.853** | Algorithmic Game Theory | 研究生 | ❌ | **完全缺失**：mechanism design、auction theory、price of anarchy |

---

## 二、6.006 Introduction to Algorithms 详细对标

**课程主页**: <https://ocw.mit.edu/courses/6-006-introduction-to-algorithms-spring-2020/>
**教材**: CLRS 3rd/4th Ed.（非必需，课程提供自编讲义）

| 主题模块 | MIT 6.006 内容 | 项目对应 | 状态 |
|---------|---------------|---------|------|
| **Module 1: Introduction** | 算法定义、效率、Python 实现 | `docs/09-算法理论/01-算法基础/` | ✅ |
| **Module 2: Sorting** | Insertion Sort、Merge Sort、Heap Sort、Quick Sort、Counting Sort | `merge_sort.rs`、`quick_sort.rs`、`heap_sort.rs`、`counting_sort.rs` | ⚠️ **Insertion Sort 缺失** |
| **Module 3: Searching** | Binary Search、Hash Tables | `binary_search.rs`、`hash_table.rs` | ✅ |
| **Module 4: Graph Algorithms** | BFS、DFS、Topological Sort、Dijkstra、Bellman-Ford | `graph_bfs_dfs.rs`、`topological_sort.rs`、`dijkstra.rs`、`bellman_ford.rs` | ✅ |
| **Module 5: Shortest Paths** | Floyd-Warshall、Johnson、A* Search | `floyd_warshall.rs`、`johnson.rs` | ⚠️ **A* Search 缺失** |
| **Module 6: Dynamic Programming** | LCS、Knapsack、Matrix Chain | `lcs.rs`、`matrix_chain.rs` | ⚠️ **0/1 Knapsack 缺失** |
| **Module 7: Greedy Algorithms** | Activity Selection、MST | `greedy_activity_selection.rs`、`graph_mst.rs` | ✅ |
| **Module 8: Advanced Topics** | Amortized Analysis、Randomized Algorithms | `docs/09-算法理论/` | ⚠️ 文档有，代码稀疏 |

**6.006 缺口**: Insertion Sort、A* Search、0/1 Knapsack

---

## 三、6.046J Design and Analysis of Algorithms 详细对标

**课程主页**: <https://ocw.mit.edu/courses/6-046j-design-and-analysis-of-algorithms-spring-2012/>
**先修**: 6.006 + 数学证明能力

| 主题模块 | 6.046J 内容 | 项目对应 | 状态 |
|---------|------------|---------|------|
| **Divide & Conquer** | 高级分治、Median of Medians、Fast Fourier Transform | `fft.rs`、`divide_and_conquer.rs` | ⚠️ Median of Medians 缺失 |
| **Dynamic Programming** | 高级 DP、Optimal BST | `optimal_bst.rs` | ✅ |
| **Greedy Algorithms** | 交换论证、拟阵 | `docs/09-算法理论/` | ⚠️ 拟阵理论覆盖不足 |
| **Graph Algorithms** | Max Flow、Min Cut、Matching | `bipartite_matching.rs` | ⚠️ Max Flow 理论文档不足 |
| **Randomized Algorithms** | QuickSelect、Hashing、Monte Carlo | `docs/09-算法理论/07-随机算法/` | ⚠️ 代码实现稀疏 |
| **Approximation Algorithms** | TSP、Set Cover、LP Rounding | `docs/09-算法理论/06-近似算法/` | 📄 有文档 |
| **NP-Completeness** | 归约、Cook-Levin | `docs/09-算法理论/05-NP完全性/` | ✅ |
| **Advanced Data Structures** | Splay Trees、Link-Cut Trees | `splay_tree.rs` | ⚠️ Link-Cut Tree 缺失 |

**6.046J 缺口**: Median of Medians、拟阵理论、Link-Cut Tree、Max Flow 深度文档

---

## 四、MIT 前沿课程（研究生级）

### 4.1 6.506 Algorithm Engineering（算法工程）

**课程主页**: <https://jshun.csail.mit.edu/6506-f25/（2025> Fall）
**授课**: Julian Shun
**先修**: 6.122 (6.046) + 6.106 (6.172)

**核心内容**（项目完全缺失）：

| 主题 | 描述 | 国际代表性论文/资源 |
|------|------|-------------------|
| **Cache-Efficient Algorithms** | 缓存无关模型 (Cache-Oblivious Model)、缓存感知模型 (Cache-Aware) | Frigo et al., "Cache-Oblivious Algorithms", FOCS 1999 |
| **External-Memory Algorithms** | 外存模型 (EM Model)、I/O 复杂度分析 | Aggarwal & Vitter, "The Input/Output Complexity of Sorting", ACM 1988 |
| **Parallel Algorithms** | PRAM 模型、Fork-Join、工作-深度分析 | Blelloch, "Programming Parallel Algorithms", CACM 1996 |
| **Write-Efficient Algorithms** | 非易失性内存 (NVM) 友好的算法设计 | Blelloch et al., "Efficient Algorithms with Asymmetric Read and Write Costs", ESA 2016 |
| **Graph Algorithm Engineering** | 大规模图处理、压缩图表示 | SNAP (Stanford Network Analysis Platform) |

**建议引入方式**：

- 在 `docs/10-高级主题/前沿算法专题/` 下新建 `算法工程/` 子目录
- 撰写 1 篇系统综述文档，涵盖上述 5 个主题
- 引用 ACM Computing Surveys 2025 年 "Methodology of Algorithm Engineering" 综述

### 4.2 6.890 Learning-Augmented Algorithms（学习增强算法）

**先修**: 6.036 或等价 + 6.046 或等价

**核心内容**（项目完全缺失）：

| 主题 | 描述 | 代表性成果 |
|------|------|-----------|
| **Learned Indexes** | 用机器学习替代传统索引结构 | Kraska et al., "The Case for Learned Index Structures", SIGMOD 2018 |
| **Learning-Augmented Streaming** | 利用预测改进流算法 | Hsu et al., "Learning-Based Frequency Estimation Algorithms", ICLR 2019 |
| **Learning-Augmented Online** | 利用预测改进在线算法 | Lykouris & Vassilvitskii, "Competitive Caching with Machine Learned Advice", ICML 2018 |
| **Learned Sketching** | 学习增强的草图数据结构 | Aamand et al., "Learned Bloom Filters", 2019 |
| **Learning-Augmented Scheduling** | 预测增强的调度算法 | Lattanzi et al., "Online Scheduling via Learned Weights", SODA 2020 |

**建议引入方式**：

- 在 `docs/10-高级主题/前沿算法专题/` 下新建 `学习增强算法/` 子目录
- 撰写 1 篇综述文档，定义 predictability/competitive ratio with predictions
- 引用 MIT 6.890 课程讲义和最新 STOC/SODA/ICML 论文

### 4.3 6.889 Sublinear Time Algorithms（亚线性时间算法）

**核心内容**（项目完全缺失）：

| 主题 | 描述 | 代表性成果 |
|------|------|-----------|
| **Property Testing** | 用亚线性查询判断对象是否满足某性质 | Goldreich, "Introduction to Property Testing", Cambridge 2017 |
| **Streaming Algorithms** | 单遍或少数几遍扫描海量数据 | Muthukrishnan, "Data Streams: Algorithms and Applications", 2005 |
| **Distribution Testing** | 用少量样本判断分布性质 | Batu et al., "Testing Properties of Distributions", FOCS 2000 |
| **Graph Parameter Estimation** | 亚线性时间估计图参数（边数、连通分量等） | Eden & Ron, "On Approximating the Number of k-cliques", STOC 2017 |

**建议引入方式**：

- 在 `docs/10-高级主题/前沿算法专题/` 下新建 `亚线性时间算法/` 子目录
- 撰写 1 篇综述文档，涵盖 property testing 和 streaming 两大方向

### 4.4 6.853 Algorithmic Game Theory（算法博弈论）

**核心内容**（项目完全缺失）：

| 主题 | 描述 | 代表性成果 |
|------|------|-----------|
| **Mechanism Design** | 激励相容的机制设计 | Nisan et al., "Algorithmic Game Theory", Cambridge 2007 |
| **Auction Theory** | 拍卖算法、收益最优拍卖 | Myerson, "Optimal Auction Design", MOR 1981 |
| **Price of Anarchy** | 自私行为导致的社会福利损失 | Koutsoupias & Papadimitriou, "Worst-case Equilibria", STACS 1999 |
| **Nash Equilibrium Computation** | 纳什均衡的计算复杂性 | Daskalakis et al., "The Complexity of Computing a Nash Equilibrium", CACM 2009 |

---

## 五、其他国际顶级课程对标

### 5.1 Stanford CS 161/261

| 课程 | 特色内容 | 项目状态 |
|------|---------|---------|
| CS 161 | 算法设计与分析（本科） | 大部分覆盖 |
| CS 261 | 高级算法与数据结构（研究生） | **缺失**: Suffix Trees、Dynamic Graphs、Succinct Data Structures |

### 5.2 CMU 15-451/651

| 课程 | 特色内容 | 项目状态 |
|------|---------|---------|
| 15-451 | Algorithm Design and Analysis | 大部分覆盖 |
| 15-651 | Advanced Algorithms | **缺失**: Metric Embeddings、Expander Graphs、Lattices |

### 5.3 ETH Zurich Algorithms Lab

| 特色 | 项目状态 |
|------|---------|
| 强调算法工程实践与理论结合 | 未对标 |

---

## 六、综合缺口汇总与优先级

### P0（最高优先级）—— 6.006 核心缺失

1. **Insertion Sort** — 最基础教学算法
2. **A* Search** — 国际课程标配启发式搜索
3. **0/1 Knapsack** — 经典 DP 教学核心

### P1 — 前沿专题引入

1. **Algorithm Engineering** — MIT 6.506（2025）核心内容
2. **Learning-Augmented Algorithms** — MIT 6.890（2024-2025）

### P2 — 进阶补全

1. **Sublinear Time Algorithms** — MIT 6.889
2. **Algorithmic Game Theory** — MIT 6.853
3. **Median of Medians / Link-Cut Tree** — 6.046J 高级内容

---

## 七、持续跟踪机制建议

1. **每学期检查 MIT OCW 更新**：<https://ocw.mit.edu/search/?q=algorithms>
2. **关注 MIT 课程目录变更**：<https://student.mit.edu/catalog/m6a.html>
3. **跟踪 Julian Shun 的课程页面**：<https://jshun.csail.mit.edu/（算法工程前沿）>
4. **订阅 ACM Computing Surveys 算法相关综述**
