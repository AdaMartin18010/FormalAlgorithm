---
title: LeetCode题号全局索引 / LeetCode Problem Global Index
version: 1.0
status: maintained
last_updated: 2026-04-23
owner: LeetCode面试专题工作组
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)

## LeetCode题号全局索引 / LeetCode Problem Global Index

### 摘要 / Executive Summary

- 本文档提供本模块（`13-LeetCode算法面试专题`）所有提及的 LeetCode 题目的全局索引，按题号排序，便于快速检索。
- 每道题目包含：题号、标题、难度、所属专题文档路径、代码文件路径、以及是否有 Lean 形式化证明。
- 本索引随专题文档的扩充而持续更新。

### 目录 / Table of Contents

- [LeetCode题号全局索引 / LeetCode Problem Global Index](#leetcode题号全局索引--leetcode-problem-global-index)
  - [摘要 / Executive Summary](#摘要--executive-summary)
  - [目录 / Table of Contents](#目录--table-of-contents)
- [1. 索引表 / Index Table](#1-索引表--index-table)
  - [1.1 数据结构专题](#11-数据结构专题)
  - [1.2 算法范式专题（关联引用）](#12-算法范式专题关联引用)
  - [1.3 图论专题](#13-图论专题)
- [2. 按专题分类索引 / Index by Topic](#2-按专题分类索引--index-by-topic)
  - [2.1 数据结构专题](#21-数据结构专题)
    - [01-数组与矩阵](#01-数组与矩阵)
    - [02-链表](#02-链表)
    - [05-二叉树与BST](#05-二叉树与bst)
  - [2.2 字符串专题](#22-字符串专题)
    - [01-字符串匹配与KMP应用](#01-字符串匹配与kmp应用)
    - [02-回文问题](#02-回文问题)
  - [2.3 算法范式专题（关联）](#23-算法范式专题关联)
    - [05-二分查找](#05-二分查找)
  - [2.4 图论专题](#24-图论专题)
    - [01-图的遍历](#01-图的遍历)
    - [02-最短路径](#02-最短路径)
    - [03-拓扑排序与DAG DP](#03-拓扑排序与dag-dp)
    - [04-最小生成树](#04-最小生成树)
- [3. 按难度分类索引 / Index by Difficulty](#3-按难度分类索引--index-by-difficulty)
  - [Easy (8 题)](#easy-8-题)
  - [Medium (21 题)](#medium-21-题)
  - [Hard (4 题)](#hard-4-题)
- [4. 代码实现语言分布 / Language Distribution](#4-代码实现语言分布--language-distribution)
  - [4.1 按语言统计](#41-按语言统计)
  - [4.2 按题目统计](#42-按题目统计)
- [5. 学习路径推荐 / Recommended Learning Path](#5-学习路径推荐--recommended-learning-path)
  - [5.1 新手路径（2 周）](#51-新手路径2-周)
  - [5.2 面试冲刺路径（1 周）](#52-面试冲刺路径1-周)

---

## 1. 索引表 / Index Table

### 1.1 数据结构专题

| 题号 | 标题 | 难度 | 所属专题 | 文档路径 | 代码路径 | Lean证明 |
|-----|------|------|---------|---------|---------|---------|
| 5 | Longest Palindromic Substring | Medium | 字符串-回文问题 | `04-字符串专题/02-回文问题.md` | `algorithms/src/leetcode/lc0005_longest_palindromic_substring.rs` | ❌ |
| 21 | Merge Two Sorted Lists | Easy | 数据结构-链表 | `01-数据结构专题/02-链表.md` | `algorithms-go/leetcode/lc0021_merge_two_sorted_lists.go` | ❌ |
| 23 | Merge k Sorted Lists | Hard | 数据结构-链表 | `01-数据结构专题/02-链表.md` | `algorithms-python/src/leetcode/lc0023_merge_k_sorted_lists.py` | ❌ |
| 28 | Implement strStr() | Easy | 字符串-KMP | `04-字符串专题/01-字符串匹配与KMP应用.md` | `algorithms/src/leetcode/lc0028_implement_strstr.rs` | ❌ |
| 48 | Rotate Image | Medium | 数据结构-数组与矩阵 | `01-数据结构专题/01-数组与矩阵.md` | `algorithms-python/src/leetcode/lc0048_rotate_image.py` | ❌ |
| 54 | Spiral Matrix | Medium | 数据结构-数组与矩阵 | `01-数据结构专题/01-数组与矩阵.md` | `algorithms-python/src/leetcode/lc0054_spiral_matrix.py` | ❌ |
| 94 | Binary Tree Inorder Traversal | Easy | 数据结构-二叉树 | `01-数据结构专题/05-二叉树与BST.md` | `algorithms/src/leetcode/lc0094_binary_tree_inorder_traversal.rs` | ❌ |
| 104 | Maximum Depth of Binary Tree | Easy | 数据结构-二叉树 | `01-数据结构专题/05-二叉树与BST.md` | `algorithms-go/leetcode/lc0104_maximum_depth_of_binary_tree.go` | ❌ |
| 141 | Linked List Cycle | Easy | 数据结构-链表 | `01-数据结构专题/02-链表.md` | 见 LC 142 | ❌ |
| 142 | Linked List Cycle II | Medium | 数据结构-链表 | `01-数据结构专题/02-链表.md` | `algorithms-go/leetcode/lc0142_linked_list_cycle_ii.go` | ❌ |
| 206 | Reverse Linked List | Easy | 数据结构-链表 | `01-数据结构专题/02-链表.md` | `algorithms-python/src/leetcode/lc0206_reverse_linked_list.py` | ❌ |
| 214 | Shortest Palindrome | Hard | 字符串-KMP | `04-字符串专题/01-字符串匹配与KMP应用.md` | `algorithms-python/src/leetcode/lc0214_shortest_palindrome.py` | ❌ |
| 226 | Invert Binary Tree | Easy | 数据结构-二叉树 | `01-数据结构专题/05-二叉树与BST.md` | `algorithms/src/leetcode/lc0226_invert_binary_tree.rs` | ❌ |
| 236 | Lowest Common Ancestor of a Binary Tree | Medium | 数据结构-二叉树 | `01-数据结构专题/05-二叉树与BST.md` | `algorithms/src/leetcode/lc0236_lowest_common_ancestor.rs` | ❌ |
| 240 | Search a 2D Matrix II | Medium | 数据结构-数组与矩阵 | `01-数据结构专题/01-数组与矩阵.md` | `algorithms-python/src/leetcode/lc0240_search_2d_matrix_ii.py` | ❌ |
| 647 | Palindromic Substrings | Medium | 字符串-回文问题 | `04-字符串专题/02-回文问题.md` | `algorithms-go/leetcode/lc0647_palindromic_substrings.go` | ❌ |

### 1.2 算法范式专题（关联引用）

| 题号 | 标题 | 难度 | 所属专题 | 文档路径 | 代码路径 | Lean证明 |
|-----|------|------|---------|---------|---------|---------|
| 33 | Search in Rotated Sorted Array | Medium | 算法范式-二分查找 | `02-算法范式专题/05-二分查找.md` | 见范式专题 | ❌ |
| 34 | Find First and Last Position of Element in Sorted Array | Medium | 算法范式-二分查找 | `02-算法范式专题/05-二分查找.md` | 见范式专题 | ❌ |
| 35 | Search Insert Position | Easy | 算法范式-二分查找 | `02-算法范式专题/05-二分查找.md` | 见范式专题 | ❌ |
| 153 | Find Minimum in Rotated Sorted Array | Medium | 算法范式-二分查找 | `02-算法范式专题/05-二分查找.md` | 见范式专题 | ❌ |
| 704 | Binary Search | Easy | 算法范式-二分查找 | `02-算法范式专题/05-二分查找.md` | 见范式专题 | ❌ |

### 1.3 图论专题

| 题号 | 标题 | 难度 | 所属专题 | 文档路径 | 代码路径 | Lean证明 |
|-----|------|------|---------|---------|---------|---------|
| 133 | Clone Graph | Medium | 图论-遍历 | `05-图论专题/01-图的遍历（DFS-BFS-并查集）.md` | `algorithms/src/leetcode/lc0133_clone_graph.rs`, `algorithms-python/src/leetcode/lc0133_clone_graph.py` | ❌ |
| 200 | Number of Islands | Medium | 图论-遍历 | `05-图论专题/01-图的遍历（DFS-BFS-并查集）.md` | `algorithms/src/leetcode/lc0200_number_of_islands.rs`, `algorithms-python/src/leetcode/lc0200_number_of_islands.py`, `algorithms-go/leetcode/lc0200_number_of_islands.go` | ❌ |
| 207 | Course Schedule | Medium | 图论-拓扑排序 | `05-图论专题/03-拓扑排序与DAG DP.md` | `algorithms/src/leetcode/lc0207_course_schedule.rs`, `algorithms-python/src/leetcode/lc0207_course_schedule.py`, `algorithms-go/leetcode/lc0207_course_schedule.go` | ❌ |
| 210 | Course Schedule II | Medium | 图论-拓扑排序 | `05-图论专题/03-拓扑排序与DAG DP.md` | `algorithms/src/leetcode/lc0210_course_schedule_ii.rs`, `algorithms-python/src/leetcode/lc0210_course_schedule_ii.py` | ❌ |
| 329 | Longest Increasing Path in a Matrix | Hard | 图论-拓扑排序 | `05-图论专题/03-拓扑排序与DAG DP.md` | 见专题文档 | ❌ |
| 743 | Network Delay Time | Medium | 图论-最短路径 | `05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md` | `algorithms/src/leetcode/lc0743_network_delay_time.rs`, `algorithms-python/src/leetcode/lc0743_network_delay_time.py`, `algorithms-go/leetcode/lc0743_network_delay_time.go` | ❌ |
| 787 | Cheapest Flights Within K Stops | Medium | 图论-最短路径 | `05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md` | `algorithms/src/leetcode/lc0787_cheapest_flights_within_k_stops.rs`, `algorithms-python/src/leetcode/lc0787_cheapest_flights_within_k_stops.py` | ❌ |
| 994 | Rotting Oranges | Medium | 图论-遍历 | `05-图论专题/01-图的遍历（DFS-BFS-并查集）.md` | `algorithms/src/leetcode/lc0994_rotting_oranges.rs`, `algorithms-go/leetcode/lc0994_rotting_oranges.go` | ❌ |
| 1135 | Connecting Cities With Minimum Cost | Medium | 图论-MST | `05-图论专题/04-最小生成树（Prim-Kruskal）.md` | 见专题文档 | ❌ |
| 1584 | Min Cost to Connect All Points | Medium | 图论-MST | `05-图论专题/04-最小生成树（Prim-Kruskal）.md` | `algorithms/src/leetcode/lc1584_min_cost_to_connect_all_points.rs` | ❌ |
| 1631 | Path With Minimum Effort | Medium | 图论-最短路径 | `05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md` | 见专题文档 | ❌ |

---

## 2. 按专题分类索引 / Index by Topic

### 2.1 数据结构专题

#### 01-数组与矩阵

- [LC 48 — Rotate Image](https://leetcode.com/problems/rotate-image/) (Medium)
- [LC 54 — Spiral Matrix](https://leetcode.com/problems/spiral-matrix/) (Medium)
- [LC 240 — Search a 2D Matrix II](https://leetcode.com/problems/search-a-2d-matrix-ii/) (Medium)

#### 02-链表

- [LC 21 — Merge Two Sorted Lists](https://leetcode.com/problems/merge-two-sorted-lists/) (Easy)
- [LC 23 — Merge k Sorted Lists](https://leetcode.com/problems/merge-k-sorted-lists/) (Hard)
- [LC 141 — Linked List Cycle](https://leetcode.com/problems/linked-list-cycle/) (Easy)
- [LC 142 — Linked List Cycle II](https://leetcode.com/problems/linked-list-cycle-ii/) (Medium)
- [LC 206 — Reverse Linked List](https://leetcode.com/problems/reverse-linked-list/) (Easy)

#### 05-二叉树与BST

- [LC 94 — Binary Tree Inorder Traversal](https://leetcode.com/problems/binary-tree-inorder-traversal/) (Easy)
- [LC 104 — Maximum Depth of Binary Tree](https://leetcode.com/problems/maximum-depth-of-binary-tree/) (Easy)
- [LC 226 — Invert Binary Tree](https://leetcode.com/problems/invert-binary-tree/) (Easy)
- [LC 236 — Lowest Common Ancestor of a Binary Tree](https://leetcode.com/problems/lowest-common-ancestor-of-a-binary-tree/) (Medium)

### 2.2 字符串专题

#### 01-字符串匹配与KMP应用

- [LC 28 — Implement strStr()](https://leetcode.com/problems/implement-strstr/) (Easy)
- [LC 214 — Shortest Palindrome](https://leetcode.com/problems/shortest-palindrome/) (Hard)

#### 02-回文问题

- [LC 5 — Longest Palindromic Substring](https://leetcode.com/problems/longest-palindromic-substring/) (Medium)
- [LC 647 — Palindromic Substrings](https://leetcode.com/problems/palindromic-substrings/) (Medium)

### 2.3 算法范式专题（关联）

#### 05-二分查找

- [LC 33 — Search in Rotated Sorted Array](https://leetcode.com/problems/search-in-rotated-sorted-array/) (Medium)
- [LC 34 — Find First and Last Position...](https://leetcode.com/problems/find-first-and-last-position-of-element-in-sorted-array/) (Medium)
- [LC 35 — Search Insert Position](https://leetcode.com/problems/search-insert-position/) (Easy)
- [LC 153 — Find Minimum in Rotated Sorted Array](https://leetcode.com/problems/find-minimum-in-rotated-sorted-array/) (Medium)
- [LC 704 — Binary Search](https://leetcode.com/problems/binary-search/) (Easy)

### 2.4 图论专题

#### 01-图的遍历

- [LC 133 — Clone Graph](https://leetcode.com/problems/clone-graph/) (Medium)
- [LC 200 — Number of Islands](https://leetcode.com/problems/number-of-islands/) (Medium)
- [LC 994 — Rotting Oranges](https://leetcode.com/problems/rotting-oranges/) (Medium)

#### 02-最短路径

- [LC 743 — Network Delay Time](https://leetcode.com/problems/network-delay-time/) (Medium)
- [LC 787 — Cheapest Flights Within K Stops](https://leetcode.com/problems/cheapest-flights-within-k-stops/) (Medium)
- [LC 1631 — Path With Minimum Effort](https://leetcode.com/problems/path-with-minimum-effort/) (Medium)

#### 03-拓扑排序与DAG DP

- [LC 207 — Course Schedule](https://leetcode.com/problems/course-schedule/) (Medium)
- [LC 210 — Course Schedule II](https://leetcode.com/problems/course-schedule-ii/) (Medium)
- [LC 329 — Longest Increasing Path in a Matrix](https://leetcode.com/problems/longest-increasing-path-in-a-matrix/) (Hard)

#### 04-最小生成树

- [LC 1135 — Connecting Cities With Minimum Cost](https://leetcode.com/problems/connecting-cities-with-minimum-cost/) (Medium)
- [LC 1584 — Min Cost to Connect All Points](https://leetcode.com/problems/min-cost-to-connect-all-points/) (Medium)

---

## 3. 按难度分类索引 / Index by Difficulty

### Easy (8 题)

| 题号 | 标题 | 所属专题 |
|-----|------|---------|
| 21 | Merge Two Sorted Lists | 链表 |
| 28 | Implement strStr() | 字符串-KMP |
| 94 | Binary Tree Inorder Traversal | 二叉树 |
| 104 | Maximum Depth of Binary Tree | 二叉树 |
| 141 | Linked List Cycle | 链表 |
| 206 | Reverse Linked List | 链表 |
| 226 | Invert Binary Tree | 二叉树 |
| 704 | Binary Search | 二分查找 |

### Medium (21 题)

| 题号 | 标题 | 所属专题 |
|-----|------|---------|
| 5 | Longest Palindromic Substring | 回文问题 |
| 33 | Search in Rotated Sorted Array | 二分查找 |
| 34 | Find First and Last Position... | 二分查找 |
| 35 | Search Insert Position | 二分查找 |
| 48 | Rotate Image | 数组与矩阵 |
| 54 | Spiral Matrix | 数组与矩阵 |
| 133 | Clone Graph | 图论-遍历 |
| 142 | Linked List Cycle II | 链表 |
| 153 | Find Minimum in Rotated Sorted Array | 二分查找 |
| 200 | Number of Islands | 图论-遍历 |
| 207 | Course Schedule | 图论-拓扑排序 |
| 210 | Course Schedule II | 图论-拓扑排序 |
| 236 | Lowest Common Ancestor of a Binary Tree | 二叉树 |
| 240 | Search a 2D Matrix II | 数组与矩阵 |
| 647 | Palindromic Substrings | 回文问题 |
| 743 | Network Delay Time | 图论-最短路径 |
| 787 | Cheapest Flights Within K Stops | 图论-最短路径 |
| 994 | Rotting Oranges | 图论-遍历 |
| 1135 | Connecting Cities With Minimum Cost | 图论-MST |
| 1584 | Min Cost to Connect All Points | 图论-MST |
| 1631 | Path With Minimum Effort | 图论-最短路径 |

### Hard (4 题)

| 题号 | 标题 | 所属专题 |
|-----|------|---------|
| 23 | Merge k Sorted Lists | 链表 |
| 214 | Shortest Palindrome | 字符串-KMP |
| 329 | Longest Increasing Path in a Matrix | 图论-拓扑排序 |

---

## 4. 代码实现语言分布 / Language Distribution

### 4.1 按语言统计

| 语言 | 题目数量 | 覆盖题号 |
|-----|---------|---------|
| Python | 11 | 5, 48, 54, 133, 200, 207, 210, 214, 240, 743, 787 |
| Rust | 12 | 5, 28, 94, 133, 200, 207, 210, 226, 236, 743, 787, 1584 |
| Go | 6 | 21, 104, 142, 200, 647, 743 |

### 4.2 按题目统计

| 题号 | Python | Rust | Go | 合计 |
|-----|--------|------|-----|------|
| 5 | ✅ | ✅ | ❌ | 2 |
| 21 | ❌ | ❌ | ✅ | 1 |
| 23 | ✅ | ❌ | ❌ | 1 |
| 28 | ❌ | ✅ | ❌ | 1 |
| 48 | ✅ | ❌ | ❌ | 1 |
| 54 | ✅ | ❌ | ❌ | 1 |
| 94 | ❌ | ✅ | ❌ | 1 |
| 104 | ❌ | ❌ | ✅ | 1 |
| 133 | ✅ | ✅ | ❌ | 2 |
| 142 | ❌ | ❌ | ✅ | 1 |
| 200 | ✅ | ✅ | ✅ | 3 |
| 206 | ✅ | ❌ | ❌ | 1 |
| 207 | ✅ | ✅ | ✅ | 3 |
| 210 | ✅ | ✅ | ❌ | 2 |
| 214 | ✅ | ❌ | ❌ | 1 |
| 226 | ❌ | ✅ | ❌ | 1 |
| 236 | ❌ | ✅ | ❌ | 1 |
| 240 | ✅ | ❌ | ❌ | 1 |
| 647 | ❌ | ❌ | ✅ | 1 |
| 743 | ✅ | ✅ | ✅ | 3 |
| 787 | ✅ | ✅ | ❌ | 2 |
| 1584 | ❌ | ✅ | ❌ | 1 |

---

## 5. 学习路径推荐 / Recommended Learning Path

### 5.1 新手路径（2 周）

**Week 1: 线性结构**

- Day 1-2: LC 206（反转链表）→ LC 21（合并链表）
- Day 3-4: LC 48（旋转图像）→ LC 54（螺旋矩阵）
- Day 5-6: LC 104（树深度）→ LC 226（翻转二叉树）
- Day 7: 复习 + 错题整理

**Week 2: 进阶与字符串**

- Day 8-9: LC 142（环检测）→ LC 236（LCA）
- Day 10-11: LC 240（矩阵搜索）→ LC 23（合并K链表）
- Day 12-13: LC 28（KMP）→ LC 5（回文串）
- Day 14: 综合复习

### 5.2 面试冲刺路径（1 周）

- Day 1: 数组矩阵专题（LC 48, 54, 240）
- Day 2: 链表专题（LC 206, 21, 142）
- Day 3: 二叉树专题（LC 94, 104, 226, 236）
- Day 4: 字符串专题（LC 28, 5, 214, 647）
- Day 5: 综合模拟面试（随机抽题）
- Day 6: 薄弱点专项突破
- Day 7: 休息 + 轻量复习

---

> **维护说明**: 本文档随专题文档的更新而同步更新。新增题目时，请按题号顺序插入到索引表中，并更新各分类统计。
