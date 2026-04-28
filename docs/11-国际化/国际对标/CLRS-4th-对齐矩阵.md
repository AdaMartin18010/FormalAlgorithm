---
title: CLRS 4th 对齐矩阵
version: 1.0
last_updated: 2026-04-19
---

# CLRS 4th Ed. 完整对齐矩阵

> **来源**: Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2022). *Introduction to Algorithms* (4th ed.). MIT Press.
> **ISBN**: 978-0-262-04630-5
> **对齐日期**: 2026-04-15

本文档将 CLRS 第 4 版（2022）的 8 个部分、35 章、4 个数学附录与项目 `docs/` 文档体系和 `examples/` 代码实现进行逐章对标，标注覆盖状态与缺口。

---

## 对齐图例

| 标记 | 含义 |
|------|------|
| ✅ | 已充分覆盖（理论文档 + 代码实现） |
| ⚠️ | 部分覆盖（有文档或代码之一，但不完整） |
| ❌ | 缺失（无对应文档且无代码实现） |
| 🆕 | CLRS 第 4 版新增内容（第 3 版无此章/节） |
| 📄 | 有理论文档 |
| 💻 | 有代码实现 |

---

## Part I: Foundations（基础）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 1 | The Role of Algorithms in Computing | `docs/01-基础理论/`、`docs/09-算法理论/01-算法基础/` | — | ⚠️ | 算法定义、效率概念有覆盖，但"算法作为技术"的经济学视角缺失 |
| Ch 2 | Getting Started（Insertion Sort + Merge Sort） | `docs/09-算法理论/01-算法基础/` | `merge_sort.rs` 💻 | ⚠️ | **Insertion Sort 完全缺失**；Merge Sort 有完整实现；循环不变式教学覆盖不足 |
| Ch 3 | Characterizing Running Times（渐近记号） | `docs/04-算法复杂度/` | — | ✅ | 大 O/Ω/Θ 记号、标准函数覆盖充分 |
| Ch 4 | Divide-and-Conquer（递归、主定理、Strassen） | `docs/09-算法理论/02-分治算法/` | `merge_sort.rs`、`divide_and_conquer.rs` 💻 | ✅ | 主定理、递归树、代入法覆盖；Strassen 矩阵乘法有实现 |
| Ch 5 | Probabilistic Analysis and Randomized Algorithms | `docs/09-算法理论/07-随机算法/` | — | 📄 | 概率分析有文档，但缺少随机化快速排序等具体实现 |

**Part I 缺口**: Insertion Sort（❌）、随机化算法具体实现（💻缺失）

---

## Part II: Sorting and Order Statistics（排序与顺序统计）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 6 | Heapsort | `docs/09-算法理论/01-算法基础/`（堆排序） | `heap_sort.rs` 💻 | ✅ | 堆排序实现完整；**Binary Heap 作为独立数据结构缺失** |
| Ch 7 | Quicksort | `docs/09-算法理论/01-算法基础/` | `quick_sort.rs` 💻 | ✅ | 快速排序实现完整 |
| Ch 8 | Sorting in Linear Time（Counting/Radix/Bucket） | `docs/09-算法理论/01-算法基础/` | `counting_sort.rs`、`radix_sort.rs`、`bucket_sort.rs` 💻 | ✅ | 三种线性时间排序均有实现 |
| Ch 9 | Medians and Order Statistics | `docs/09-算法理论/01-算法基础/`（quick_select） | `quick_select.rs` 💻 | ⚠️ | 顺序统计量、中位数有 quick_select；**最坏情况线性时间选择算法（median of medians）缺失** |

**Part II 缺口**: Binary Heap 独立模块（❌）、Median of Medians（❌）

---

## Part III: Data Structures（数据结构）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 10 | Elementary Data Structures（栈、队列、链表、根树） | `docs/08-实现示例/` | `stack.rs`、`queue.rs`、`linked_list.rs` 💻 | ✅ | 基础数据结构实现完整 |
| Ch 11 | Hash Tables | `docs/08-实现示例/` | `hash_table.rs` 💻 | ✅ | 分离链接法和开放寻址法均有实现 |
| Ch 12 | Binary Search Trees | — | — | ❌ | **普通 BST 无独立文档和实现**（直接跳到红黑树/AVL/B树） |
| Ch 13 | Red-Black Trees | `docs/08-实现示例/` | `red_black_tree.rs` 💻 | ✅ | 红黑树实现完整 |
| 🆕 Ch 14 | Augmenting Data Structures（顺序统计树、区间树） | `docs/08-实现示例/` | `interval_tree.rs` 💻 | ⚠️ | 区间树有实现；顺序统计树（Order Statistic Tree）缺失 |

**Part III 缺口**: 普通 Binary Search Tree（❌）、Order Statistic Tree（❌）

---

## Part IV: Advanced Design and Analysis Techniques（高级设计与分析）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 15 | Dynamic Programming | `docs/09-算法理论/`（DP相关） | `lcs.rs`、`matrix_chain.rs`、`optimal_bst.rs` 💻 | ⚠️ | 经典 DP（LCS、矩阵链、最优BST）有实现；**0/1 Knapsack、LIS、Coin Change 缺失** |
| Ch 16 | Greedy Algorithms | `docs/09-算法理论/` | `greedy_activity_selection.rs`、`graph_mst.rs` 💻 | ✅ | 活动选择、MST（Kruskal/Prim）有实现 |
| Ch 17 | Amortized Analysis | `docs/04-算法复杂度/` | `fibonacci_heap.rs` 💻 | ⚠️ | 摊还分析概念有文档；**势能方法、聚合分析的具体教学案例不足** |

**Part IV 缺口**: 0/1 Knapsack（❌）、LIS（❌）、Coin Change（❌）、摊还分析教学案例（⚠️）

---

## Part V: Advanced Data Structures（高级数据结构）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 18 | B-Trees | `docs/08-实现示例/` | `b_tree.rs` 💻 | ✅ | B树实现完整 |
| Ch 19 | Data Structures for Disjoint Sets（Union-Find） | `docs/08-实现示例/` | `union_find.rs` 💻 | ✅ | 并查集实现完整（路径压缩 + 按秩合并） |
| 🆕 Ch 20 | van Emde Boas Trees | `docs/08-实现示例/` | `van_emde_boas.rs` 💻 | ✅ | vEB 树实现完整 |

**Part V 缺口**: 无显著缺口

---

## Part VI: Graph Algorithms（图算法）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 21 | Elementary Graph Algorithms（BFS/DFS/拓扑） | `docs/09-算法理论/09-图算法高级/` | `graph_bfs_dfs.rs`、`topological_sort.rs` 💻 | ✅ | BFS/DFS/拓扑排序实现完整 |
| Ch 22 | Minimum Spanning Trees | `docs/09-算法理论/09-图算法高级/` | `graph_mst.rs` 💻 | ✅ | Kruskal + Prim 实现完整 |
| Ch 23 | Single-Source Shortest Paths（Dijkstra/Bellman-Ford） | `docs/09-算法理论/09-图算法高级/` | `dijkstra.rs`、`bellman_ford.rs` 💻 | ✅ | Dijkstra + Bellman-Ford 实现完整 |
| Ch 24 | All-Pairs Shortest Paths（Floyd-Warshall/Johnson） | `docs/09-算法理论/09-图算法高级/` | `floyd_warshall.rs`、`johnson.rs` 💻 | ✅ | Floyd-Warshall + Johnson 实现完整 |
| 🆕 Ch 25 | Matchings in Bipartite Graphs | — | `bipartite_matching.rs` 💻 | ⚠️ | **匈牙利算法有实现，但无系统理论文档**；Hall 定理、Kőnig 定理、Hopcroft-Karp 复杂度分析缺失 |

**Part VI 缺口**: A* Search（❌，CLRS未涵盖但国际课程标配）、二分图匹配理论文档（⚠️）

---

## Part VII: Selected Topics（选学主题）

| 章 | 标题 | 项目 docs 对应 | 项目 code 对应 | 状态 | 备注 |
|---|------|---------------|---------------|------|------|
| Ch 26 | Parallel Algorithms | `docs/10-高级主题/` | — | 📄 | 并行算法有概念文档，但无具体实现 |
| 🆕 Ch 27 | Online Algorithms | `docs/09-算法理论/08-在线算法/` | — | ⚠️ | 在线算法有基础文档；**competitive ratio 系统分析、ski rental、paging、k-server 等经典问题覆盖不足** |
| Ch 28 | Matrix Operations（Strassen/LUP） | `docs/08-实现示例/` | `matrix_operations.rs`、`lup_decomposition.rs` 💻 | ✅ | Strassen + LUP 实现完整 |
| Ch 29 | Linear Programming | `docs/03-优化理论/` | — | 📄 | 线性规划有优化理论文档，但无算法实现（单纯形法等） |
| Ch 30 | Polynomials and the FFT | `docs/08-实现示例/` | `fft.rs`、`polynomial.rs` 💻 | ✅ | FFT + 多项式运算实现完整 |
| Ch 31 | Number-Theoretic Algorithms | `docs/09-算法理论/数论算法/` | `extended_euclidean.rs`、`primality_test.rs`、`discrete_log.rs` 💻 | ✅ | 数论算法覆盖较全 |
| 🆕 Ch 32 | String Matching（KMP等） | `docs/09-算法理论/04-字符串算法/` | `rabin_karp.rs`、`z_algorithm.rs`、`manacher.rs`、`ac_automaton.rs` 💻 | ⚠️ | **KMP 算法缺失**；Rabin-Karp、Z算法、Manacher、AC自动机有实现；后缀数组（SA-IS/DC3）实现缺失 |
| 🆕 Ch 33 | Machine-Learning Algorithms | — | — | ❌ | **完全缺失**：perceptron、SVM、梯度下降、神经网络基础 |
| Ch 34 | NP-Completeness | `docs/09-算法理论/05-NP完全性/` | — | 📄 | NP完全性理论文档充分 |
| Ch 35 | Approximation Algorithms | `docs/09-算法理论/06-近似算法/` | — | 📄 | 近似算法理论文档充分 |

**Part VII 缺口**: Online Algorithms 深度（⚠️）、KMP（❌）、Suffix Arrays 实现（❌）、**ML Algorithms（❌）**、A* Search（❌，虽非CLRS章节但为国际标配）

---

## Appendix（数学基础）

| 附录 | 标题 | 项目 docs 对应 | 状态 |
|------|------|---------------|------|
| A | Summations（求和） | `docs/01-基础理论/` | ✅ |
| B | Sets, Etc.（集合论） | `docs/01-基础理论/` | ✅ |
| C | Counting and Probability（计数与概率） | `docs/01-基础理论/`、概率相关文档 | ✅ |
| D | Matrices（矩阵） | `docs/01-基础理论/` | ✅ |

---

## 总结统计

| 状态 | 章节数 | 占比 |
|------|--------|------|
| ✅ 充分覆盖 | 20 章 | ~57% |
| ⚠️ 部分覆盖 | 8 章 | ~23% |
| ❌ 缺失 | 7 章 | ~20% |

**最关键的 7 个缺失项（按优先级排序）**：

1. **🆕 Ch 33 Machine-Learning Algorithms** — 第 4 版全新章节，项目完全空白
2. **Ch 2 Insertion Sort** — 最基础教学算法，项目无独立文档和实现
3. **Ch 12 Binary Search Trees** — 基础数据结构，项目直接跳过到平衡树
4. **A* Search** — 虽非 CLRS 章节，但是 MIT 6.006/Stanford CS161 等国际课程标配，项目完全缺失
5. **🆕 Ch 27 Online Algorithms** — 第 4 版新增章节，文档零散，无系统覆盖
6. **Ch 15 经典 DP（Knapsack/LIS/Coin Change）** — 教学与面试核心，项目缺失
7. **Ch 6 Binary Heap（独立模块）** — 核心数据结构，仅作为 heap_sort 内部使用

**第 4 版新增内容（🆕）覆盖状态**：

- Ch 14 Augmenting Data Structures → ⚠️ 部分覆盖
- Ch 20 van Emde Boas Trees → ✅ 已覆盖
- Ch 25 Matchings in Bipartite Graphs → ⚠️ 部分覆盖（有代码无理论）
- Ch 27 Online Algorithms → ⚠️ 部分覆盖
- Ch 32 String Matching（扩展）→ ⚠️ 部分覆盖（KMP 缺失）
- Ch 33 Machine-Learning Algorithms → ❌ 完全缺失

---

## 下一步行动建议

1. **最高优先级**：补齐 Ch 33 ML Algorithms、Ch 2 Insertion Sort、A* Search 的理论文档
2. **高优先级**：补齐 Binary Heap 独立模块、经典 DP（Knapsack/LIS/Coin Change）
3. **中优先级**：深度覆盖 Ch 27 Online Algorithms、Ch 25 二分图匹配理论
4. **持续跟踪**：CLRS 官方网站（mitpress.mit.edu）的勘误与补充材料
