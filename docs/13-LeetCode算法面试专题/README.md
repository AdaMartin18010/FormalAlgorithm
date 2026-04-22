---
title: LeetCode算法面试专题目录 / LeetCode Algorithm Interview Specialization Index
version: 1.0
status: maintained
last_updated: 2026-04-23
owner: LeetCode面试专题工作组
concepts: ["面试准备", "算法实战", "LeetCode", "目录索引", "学习路径"]
level: 全级别
---

# LeetCode 算法面试专题

> 形式化算法库的核心实战模块，覆盖 LeetCode 高频面试题的形式化分析、多语言实现与严格证明。

## 模块简介

本专题将 LeetCode 经典面试题按**数据结构**、**算法范式**、**数学专题**、**字符串**、**图论**和**面试实战**六大板块进行系统梳理。每道题目均遵循「四步法」解题框架：

1. **形式化规约**：将题目转化为精确的数学描述；
2. **算法设计**：给出伪代码与复杂度分析；
3. **正确性证明**：使用循环不变式、归纳法或反证法证明；
4. **参考实现**：提供 Rust / Python / Go 等多语言代码。

此外，部分题目还配备了 **Lean 4 形式化证明**，确保证明的机器可检验性。

## 子目录简介与推荐阅读顺序

本模块共 8 个子目录，覆盖从方法论到实战的完整闭环：

| 序号 | 子目录 | 简介 | 推荐阅读时机 |
|------|--------|------|--------------|
| 00 | [00-总览与方法论](00-总览与方法论/) | 专题导论、「四步法」解题框架、复杂度速查与面试沟通模板 | **必读**：开始任何专题前 |
| 01 | [01-数据结构专题](01-数据结构专题/) | 数组、链表、栈/队列、哈希表、二叉树与 BST、堆、并查集、Trie | 基础夯实阶段 |
| 02 | [02-算法范式专题](02-算法范式专题/) | 枚举、双指针、滑动窗口、前缀和、二分、分治、贪心、动态规划、回溯、BFS、位运算 | 核心算法阶段 |
| 03 | [03-数学专题](03-数学专题/) | 数论、组合数学、计算几何、概率与随机算法 | 进阶提升或查漏补缺 |
| 04 | [04-字符串专题](04-字符串专题/) | 字符串匹配（KMP）、回文问题、字符串动态规划 | 需要强化字符串时 |
| 05 | [05-图论专题](05-图论专题/) | 遍历、最短路径、拓扑排序、最小生成树 | 图论薄弱时 |
| 06 | [06-面试专题](06-面试专题/) | 高频 Top 100、剑指 Offer 形式化证明、大厂真题分类 | 面试冲刺阶段 |
| 99 | [99-附录](99-附录/) | LeetCode 题号全局索引、常见错误清单、多语言代码模板速查 | 随时查阅 |

**标准阅读顺序**：`00` → `01` → `02` → `03~05`（按需） → `06` → `99`（参考）。

---

## 快速开始指南

### 路径一：刷题路径（Systematic Practice）
>
> 目标：系统掌握 LeetCode 高频题，建立完整知识体系。

1. [专题导论](00-总览与方法论/00-专题导论.md) → 理解模块定位与「四步法」；
2. [数据结构专题](01-数据结构专题/) → 逐个攻克基础数据结构；
3. [算法范式专题](02-算法范式专题/) → 深入掌握核心算法思想；
4. [面试专题](06-面试专题/) → 用高频题与大厂真题检验成果；
5. [附录代码模板](99-附录/03-多语言代码模板速查.md) → 考前速查。

### 路径二：形式化证明路径（Formal Verification）
>
> 目标：不仅写出代码，更能严格证明算法正确性。

1. [解题方法论](00-总览与方法论/01-解题方法论（四步法与形式化思维）.md) → 建立形式化思维；
2. 任选专题中的「形式化证明」章节（如 [动态规划](02-算法范式专题/08-动态规划.md) 或 [二分查找](02-算法范式专题/05-二分查找.md)）；
3. 对照 [Lean 4 形式化证明](../../examples/lean_proofs/FormalAlgorithm/leetcode/) 阅读机器可检验的证明；
4. 尝试为经典题目补充循环不变式或归纳证明。

### 路径三：面试冲刺路径（Interview Sprint）
>
> 目标：在有限时间内最大化面试通过率。

1. [复杂度速查与面试沟通模板](00-总览与方法论/02-复杂度速查与面试沟通模板.md) → 快速恢复面试状态；
2. [高频 Top 100](06-面试专题/01-高频Top100-数组与链表.md)、[树与图](06-面试专题/02-高频Top100-树与图.md)、[DP 与贪心](06-面试专题/03-高频Top100-DP与贪心.md) → 精刷核心题；
3. [大厂真题分类](06-面试专题/05-大厂真题分类（字节-阿里-腾讯-Google）.md) → 了解目标公司考察偏好；
4. [常见错误清单](99-附录/02-面试常见错误清单.md) → 避开高频失分点。

---

## 代码实现索引

各语言实现入口如下：

| 语言 | 路径 | 说明 |
|------|------|------|
| Rust（主仓库） | [`examples/algorithms/src/leetcode/`](../../examples/algorithms/src/leetcode/) | 主要实现语言，71 题 |
| Rust（补充） | [`examples/algorithms/src/leetcode/`](../../examples/algorithms/src/leetcode/) | 额外 Rust 实现 |
| Python | [`examples/algorithms-python/src/leetcode/`](../../examples/algorithms-python/src/leetcode/) | 辅助教学语言，代码简洁易读 |
| Go | [`examples/algorithms-go/leetcode/`](../../examples/algorithms-go/leetcode/) | 工程实践语言，附带单测 |
| Lean 4 | [`examples/lean_proofs/FormalAlgorithm/leetcode/`](../../examples/lean_proofs/FormalAlgorithm/leetcode/) | 形式化证明，机器可检验 |

> 注：代码文件命名遵循 `lcXXXX_problem_name.ext` 规范，与附录题号索引一一对应。

## 题号覆盖统计

- **索引题号总数**：84
- **代码实现题号数**：84
- **文档覆盖题号数**：80
- **代码+文档完全覆盖**：80
- **形式化证明题号数**：14

### 按难度分布

| 难度 | 数量 |
|------|------|
| 简单 | 19 |
| 中等 | 53 |
| 困难 | 12 |

### 按算法范式/数据结构分布

| 分类 | 数量 |
|------|------|
| 数组与矩阵 | 30 |
| 字符串 | 10 |
| 二叉树与BST | 6 |
| 数学 | 5 |
| 栈与队列 | 5 |
| 链表 | 5 |
| 动态规划 | 5 |
| 图论 | 5 |
| 位运算 | 4 |
| 回溯与DFS | 2 |
| 算法范式 | 2 |
| BFS与图搜索 | 2 |
| 哈希表 | 1 |
| 并查集 | 1 |
| 贪心算法 | 1 |

## 语言覆盖统计

| 语言 | 实现题数 | 说明 |
|------|----------|------|
| Rust | 71 | 主要实现语言，包含在 `examples/algorithms/` |
| Python | 80 | 辅助教学语言，代码简洁易读 |
| Go | 60 | 工程实践语言，附带单测 |
| Lean 4 | 14 | 形式化证明语言，机器可检验 |

## Lean 4 形式化证明索引

以下题目已完成 **Lean 4 形式化证明**，代表本模块在形式化验证方面的核心成果。证明文件位于 [`examples/lean_proofs/FormalAlgorithm/leetcode/`](../../examples/lean_proofs/FormalAlgorithm/leetcode/)。

| 题号 | 题目名称 | 证明要点 | Lean 4 证明文件 |
|------|----------|----------|----------------|
| 1 | Two Sum | 解的存在性与唯一性条件 | [`lc0001_two_sum.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0001_two_sum.lean) |
| 3 | Longest Substring Without Repeating Characters | 滑动窗口不变式 | [`lc0003_longest_substring.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0003_longest_substring.lean) |
| 15 | 3Sum | 双指针正确性 | [`lc0015_3sum.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0015_3sum.lean) |
| 21 | Merge Two Sorted Lists | 链表归并的终止性 | [`lc0021_merge_two_sorted_lists.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0021_merge_two_sorted_lists.lean) |
| 53 | Maximum Subarray | Kadane 算法最优性子结构 | [`lc0053_maximum_subarray.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0053_maximum_subarray.lean) |
| 70 | Climbing Stairs | 斐波那契递推的数学归纳 | [`lc0070_climbing_stairs.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0070_climbing_stairs.lean) |
| 72 | Edit Distance | DP 状态转移正确性 | [`lc0072_edit_distance.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0072_edit_distance.lean) |
| 104 | Maximum Depth of Binary Tree | 树高定义的递归等价 | [`lc0104_maximum_depth_of_binary_tree.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0104_maximum_depth_of_binary_tree.lean) |
| 136 | Single Number | 异或运算的交换律与消去律 | [`lc0136_single_number.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0136_single_number.lean) |
| 141 | Linked List Cycle | Floyd 判圈算法的正确性 | [`lc0141_linked_list_cycle.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0141_linked_list_cycle.lean) |
| 198 | House Robber | DP 最优子结构归纳证明 | [`lc0198_house_robber.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0198_house_robber.lean) |
| 200 | Number of Islands | DFS 连通分量计数 | [`lc0200_number_of_islands.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0200_number_of_islands.lean) |
| 207 | Course Schedule | 拓扑排序与环检测的等价性 | [`lc0207_course_schedule.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0207_course_schedule.lean) |
| 704 | Binary Search | 循环不变式与终止性 | [`lc0704_binary_search.lean`](../../examples/lean_proofs/FormalAlgorithm/leetcode/lc0704_binary_search.lean) |

> 更多证明持续补充中，欢迎参考 [Lean 4 形式化证明目录](../../examples/lean_proofs/FormalAlgorithm/leetcode/) 获取最新进展。

## 与项目其他模块的交叉引用

| 本模块内容 | 关联模块 | 说明 |
|------------|----------|------|
| 形式化证明方法 | `03-形式化证明/` | 本模块的「四步法」与循环不变式来源于项目统一的形式化证明体系 |
| 复杂度分析 | `04-算法复杂度/` | 专题中的复杂度速查表与复杂度理论文档相互补充 |
| 动态规划理论 | `09-算法理论/01-算法基础/06-动态规划理论-六维补充.md` | 面试专题侧重实战，理论文档提供严格定义与定理证明 |
| 图算法理论 | `09-算法理论/01-算法基础/05-图算法理论-六维补充.md` | 图论专题的实战题目与理论文档的六维分析形成闭环 |
| 递归与归纳 | `02-递归理论/` | 动态规划、回溯等范式的正确性证明依赖递归理论 |
| 类型与逻辑 | `05-类型理论/`、`06-逻辑系统/` | 形式化规约与 Lean 4 证明的底层基础 |
| 计算模型 | `07-计算模型/` | 复杂度分类与可计算性边界在算法选型中的指导作用 |

## 与外部资源的对齐表

### NeetCode 150

NeetCode 150 是业界广泛认可的刷题清单。以下是我们已覆盖的 NeetCode 题目：

| NeetCode 分类 | 本模块对应章节 | 覆盖题号示例 |
|---------------|----------------|--------------|
| Arrays & Hashing | `01-数据结构专题/04-哈希表` | 1, 136 |
| Two Pointers | `02-算法范式专题/02-双指针` | 11, 15, 26, 141, 142, 167 |
| Sliding Window | `02-算法范式专题/03-滑动窗口` | 3, 76, 209 |
| Stack | `01-数据结构专题/03-栈与队列` | 20, 155, 232 |
| Binary Search | `02-算法范式专题/05-二分查找` | 33, 153, 704 |
| Linked List | `01-数据结构专题/02-链表` | 21, 141, 142, 206 |
| Trees | `01-数据结构专题/05-二叉树与BST` | 94, 96, 102, 104, 226, 236 |
| Heap / Priority Queue | `01-数据结构专题/06-堆与优先队列` | 23, 239 |
| Backtracking | `02-算法范式专题/09-回溯与DFS` | 37, 39, 46, 51, 79 |
| Tries | `01-数据结构专题/08-Trie树` | — |
| Graphs | `05-图论专题` | 127, 133, 200, 207, 210, 743, 787, 994, 1584 |
| Advanced Graphs | `05-图论专题` | — |
| 1-D DP | `02-算法范式专题/08-动态规划` | 70, 198, 300, 322, 416 |
| 2-D DP | `02-算法范式专题/08-动态规划` | 72, 1143, 312 |
| Greedy | `02-算法范式专题/07-贪心算法` | 45, 55, 435, 455 |
| Intervals | `02-算法范式专题/07-贪心算法` | 435 |
| Math & Geometry | `03-数学专题` | 9, 48, 50, 204 |
| Bit Manipulation | `02-算法范式专题/11-位运算` | 136, 137, 191, 260, 338 |

### Blind 75

| Blind 75 分类 | 本模块对应章节 | 覆盖状态 |
|---------------|----------------|----------|
| Array | `01-数据结构专题/01-数组与矩阵` | 大部分覆盖 |
| Binary | `02-算法范式专题/05-二分查找` | 已覆盖 |
| DP | `02-算法范式专题/08-动态规划` | 已覆盖 |
| Graph | `05-图论专题` | 已覆盖 |
| Interval | `02-算法范式专题/07-贪心算法` | 已覆盖 |
| Linked List | `01-数据结构专题/02-链表` | 已覆盖 |
| Matrix | `01-数据结构专题/01-数组与矩阵` | 已覆盖 |
| String | `04-字符串专题` | 已覆盖 |
| Tree | `01-数据结构专题/05-二叉树与BST` | 已覆盖 |
| Heap | `01-数据结构专题/06-堆与优先队列` | 部分覆盖 |

### 剑指 Offer

| 剑指 Offer 题号 | 本模块位置 | 代码实现 |
|-----------------|------------|----------|
| 03 | `06-面试专题/04-剑指Offer精选形式化证明` | Python |
| 09 | `06-面试专题/04-剑指Offer精选形式化证明` | Go |
| 10-I | `06-面试专题/04-剑指Offer精选形式化证明` | Rust |

> 注：本模块的「剑指 Offer」部分侧重于**形式化证明**而非完整代码实现。

---

## 贡献指南

1. 新增题目请遵循 `lcXXXX_problem_name.rs` 的命名规范；
2. 文档中引用题号时，请确保在附录索引中同步更新；
3. 形式化证明优先使用 `lean_proofs/FormalAlgorithm/leetcode/` 目录；
4. 提交前运行 `scripts/generate_leetcode_index.py` 更新全局索引。
