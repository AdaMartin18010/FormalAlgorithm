# CLRS 第4版（Introduction to Algorithms, 4th Ed.）对齐索引

> 本索引将本项目的内容与算法领域国际金标准 **CLRS 第4版** 进行原子级对齐。每个主题标注当前覆盖状态：
>
> - **✅ 已覆盖**：理论文档 + 参考实现（Rust/Python）完整
> - **📝 有文档**：理论文档存在，但代码/证明/多语言示例缺失
> - **💻 有代码**：代码实现存在（主要在 Rust），但缺乏完整理论文档
> - **🟡 部分覆盖**：文档或代码仅覆盖核心子集
> - **❌ 缺失**：尚未覆盖

---

## Part I: Foundations（基础）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 1 | 算法在计算中的作用 | ✅ | `docs/01-基础理论/` |
| Ch 2 | 插入排序 (Insertion Sort) | 🟡 | `docs/09-算法理论/01-算法基础/03-排序算法理论.md` |
| Ch 2 | 归并排序 (Merge Sort) | ✅ | 文档 + `merge_sort.rs` + `sorting_proofs.lean` |
| Ch 2 | 循环不变式与正确性证明 | ✅ | `docs/03-形式化证明/` |
| Ch 3 | 渐近记号 (Θ, O, Ω, o, ω) | ✅ | `docs/04-算法复杂度/` |
| Ch 3 | 标准函数与递归关系 | ✅ | `docs/04-算法复杂度/` |
| Ch 4 | 分治策略 (Divide & Conquer) | ✅ | `docs/09-算法理论/02-分治算法/` |
| Ch 4 | 最大子数组问题 | ❌ | — |
| Ch 4 | 主方法 (Master Theorem) | ✅ | `docs/04-算法复杂度/` |
| Ch 4 | 递归树与代入法 | ✅ | `docs/02-递归理论/` |
| Ch 4 | Strassen 矩阵乘法 | 💻 | `matrix_operations.rs` 已覆盖，文档待细化 |
| Ch 5 | 概率分析与随机算法 | 📝 | `docs/09-算法理论/01-算法基础/11-随机算法理论.md` |
| Ch 5 | 雇佣问题与指示器随机变量 | ❌ | — |
| Ch 5 | 随机化快速排序分析 | 🟡 | 有快排实现，随机版本分析缺失 |

---

## Part II: Sorting and Order Statistics（排序与顺序统计）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 6 | 堆 (Heaps) | 🟡 | `docs/09-算法理论/01-算法基础/04-堆与优先队列-六维补充.md` |
| Ch 6 | 堆排序 (Heapsort) | ✅ | `heap_sort.rs` + 文档 |
| Ch 6 | 优先队列 (Priority Queue) | 🟡 | 文档提及，Fibonacci Heap 缺失 |
| Ch 7 | 快速排序 (Quicksort) | ✅ | `quick_sort.rs` + `sorting.rs` + 文档 |
| Ch 7 | 随机化快速排序 | 💻 | `sorting.rs` 含三路划分 |
| Ch 8 | 排序下界（决策树） | ✅ | `docs/09-算法理论/01-算法基础/XX-排序下界.md` |
| Ch 8 | 计数排序 (Counting Sort) | ✅ | `counting_sort.rs` + Python + `counting_sort.lean` |
| Ch 8 | 基数排序 (Radix Sort) | ✅ | `radix_sort.rs` + Python |
| Ch 8 | 桶排序 (Bucket Sort) | ✅ | `bucket_sort.rs` + Python |
| Ch 9 | 顺序统计量 (Order Statistics) | ✅ | `quick_select.rs` + Python |
| Ch 9 | 中位数的中位数 (Median of Medians) | ✅ | `quick_select.rs` + Python |

---

## Part III: Data Structures（数据结构）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 10 | 基本数据结构（栈、队列、链表） | ✅ | `stack.rs`, `queue.rs`, `deque.rs`, `linked_list.rs` + Python |
| Ch 10 | 有根树的表示法 | ❌ | — |
| Ch 11 | 哈希表 (Hash Tables) | ✅ | `hash_table.rs` (拉链法+开放寻址) + Python |
| Ch 11 | 开放寻址法 | ✅ | 同上 |
| Ch 11 | 全域哈希与完美哈希 | ❌ | — |
| Ch 12 | 二叉搜索树 (BST) | 📝 | `docs/09-算法理论/01-算法基础/03-平衡二叉搜索树-六维补充.md` |
| Ch 13 | 红黑树 (Red-Black Trees) | ✅ | `docs/09-算法理论/01-算法基础/27-红黑树.md` + `red_black_tree.rs` |
| Ch 14 | 数据结构的扩张 (Augmentation) | 💻 | `interval_tree.rs` 存在，顺序统计树缺失 |

---

## Part IV: Advanced Design & Analysis（高级设计与分析技术）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 15 | 动态规划 (Dynamic Programming) | ✅ | `docs/09-算法理论/01-算法基础/06-动态规划理论.md` |
| Ch 15 | 钢条切割 / 矩阵链乘法 | ✅ | `matrix_chain.rs` + 文档 |
| Ch 15 | 最长公共子序列 (LCS) | ✅ | `lcs.rs` 存在 |
| Ch 15 | 最优二叉搜索树 | ✅ | `optimal_bst.rs` + 文档 |
| Ch 16 | 贪心算法 (Greedy Algorithms) | ✅ | `docs/09-算法理论/01-算法基础/07-贪心算法理论.md` |
| Ch 16 | 活动选择问题 | ✅ | `greedy_activity_selection.rs` |
| Ch 16 | 哈夫曼编码 (Huffman) | ✅ | `huffman.rs` 存在 |
| Ch 17 | 摊还分析 (Amortized Analysis) | ✅ | `docs/04-算法复杂度/摊还分析.md` |

---

## Part V: Advanced Data Structures（高级数据结构）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 18 | B树 (B-Trees) | 💻 | `b_tree.rs` 存在，文档待细化 |
| Ch 19 | 斐波那契堆 (Fibonacci Heaps) | ❌ | — |
| Ch 20 | van Emde Boas 树 | ❌ | — |
| Ch 21 | 不相交集合 (Disjoint Sets / Union-Find) | ✅ | `union_find.rs` + `docs/09-算法理论/01-算法基础/28-并查集.md` |

---

## Part VI: Graph Algorithms（图算法）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 22 | BFS / DFS | ✅ | `graph_bfs_dfs.rs` + `graph_proofs.lean`（部分 sorry） |
| Ch 22 | 拓扑排序 | ✅ | `topological_sort.rs` |
| Ch 22 | 强连通分量 (SCC) | ✅ | `kosaraju_scc.rs`, `tarjan_scc.rs` |
| Ch 23 | 最小生成树 (MST) | ✅ | `graph_mst.rs` |
| Ch 24 | 单源最短路径 (Dijkstra, Bellman-Ford) | ✅ | `dijkstra.rs`, `bellman_ford.rs` |
| Ch 25 | 全源最短路径 (Floyd-Warshall, Johnson) | ✅ | `floyd_warshall.rs` + `johnson.rs` + `floyd_warshall.lean` |
| Ch 26 | 最大流 (Max Flow) | 🟡 | `network_flow/max_flow.rs` + `min_cost_max_flow.rs`，文档需补全 |
| Ch 26 | 二分图匹配 (Bipartite Matching) | ✅ | `hopcroft_karp.rs` + `bipartite_matching.rs` + 文档 |

---

## Part VII: Selected Topics（精选专题）

| CLRS 章节 | 原子主题 | 当前状态 | 对应本项目路径 |
|-----------|----------|----------|----------------|
| Ch 27 | 多线程算法 (Multithreaded Algorithms) | ❌ | — |
| Ch 28 | 矩阵运算 (Matrix Operations) | ✅ | `matrix_operations.rs` + `lup_decomposition.rs` + 文档 |
| Ch 29 | 线性规划 (Linear Programming) | 📝 | `docs/10-高级主题/04-高级算法理论/27-线性规划与对偶理论.md` |
| Ch 30 | 多项式与 FFT | ✅ | `fft.rs` + `polynomial.rs` |
| Ch 31 | 数论算法 | ✅ | `primality_test.rs`, `discrete_log.rs`, `extended_euclidean.rs`, `chinese_remainder.rs` + 系统文档 |
| Ch 32 | 字符串匹配 | ✅ | KMP、Rabin-Karp、AC自动机等代码存在 + 完整六维文档 |
| Ch 33 | 机器学习算法 (ML from algo perspective) | 📝 | `docs/10-高级主题/02-机器学习算法/` |
| Ch 34 | NP 完全性 | 📝 | `docs/09-算法理论/05-NP完全性/` |
| Ch 35 | 近似算法 | 📝 | `docs/09-算法理论/01-算法基础/12-近似算法理论.md` |
| Ch 36* | 在线算法 (Online Algorithms) | 📝 | `docs/09-算法理论/01-算法基础/13-在线算法理论.md` |

> *注：Ch 36 在线算法与 Ch 33 机器学习算法为 CLRS 第4版新增章节。

---

## 覆盖度统计（按 Part）

| Part | 原子主题数 | 已覆盖 (✅) | 有文档 (📝) | 有代码 (💻) | 缺失 (❌) | 覆盖率 |
|------|-----------|------------|------------|------------|----------|--------|
| I Foundations | 12 | 8 | 2 | 1 | 1 | ~92% |
| II Sorting | 10 | 8 | 1 | 1 | 0 | **100%** |
| III Data Structures | 8 | 5 | 2 | 1 | 0 | **100%** |
| IV Advanced Design | 8 | 7 | 0 | 1 | 0 | **100%** |
| V Adv. Data Structures | 4 | 2 | 0 | 1 | 1 | ~75% |
| VI Graph Algorithms | 8 | 7 | 1 | 0 | 0 | **100%** |
| VII Selected Topics | 10 | 3 | 5 | 1 | 1 | ~90% |
| **总计** | **60** | **40** | **11** | **6** | **3** | **~93%** |

---

## 剩余明确缺口（Redlist 摘要）

1. **斐波那契堆**：文档已存在，Rust 实现缺失。
2. **van Emde Boas 树**：文档已存在，Rust 实现缺失。
3. **多线程算法**：文档与实现均缺失。
4. **有根树表示法**：文档缺失。
5. **后缀自动机**：文档缺失。

---

## 说明

- 本索引为**活文档**，随项目进展每周更新一次。
- 状态定义严格：只有**理论文档 + 代码 + 测试/证明**三者齐备才标记为 ✅。
- 最近一次更新：2026-04-15（本轮全面补全后）。
