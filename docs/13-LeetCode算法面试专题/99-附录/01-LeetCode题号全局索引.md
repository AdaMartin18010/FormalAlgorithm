---
title: 附录一：LeetCode题号全局索引 / Appendix I：LeetCode Problem Index
version: 1.0
status: maintained
last_updated: 2026-04-23
owner: LeetCode面试专题工作组
concepts: ["索引", "LeetCode", "题号映射", "全局导航"]
level: 全级别
---

# 附录一：LeetCode 题号全局索引

> 本索引由自动化脚本生成，覆盖 `docs/13-LeetCode算法面试专题/` 全部文档与 `examples/*` 下全部代码实现。
> 最后更新：2026-04-23

## 概览统计

| 指标 | 数值 |
|------|------|
| 索引题号总数 | 84 |
| 有代码实现 | 84 |
| 有文档覆盖 | 80 |
| 代码+文档完全覆盖 | 80 |
| 有形式化证明 (Lean) | 14 |

### 按难度分布

| 难度 | 数量 |
|------|------|
| 简单 | 19 |
| 中等 | 53 |
| 困难 | 12 |
| 未知 | 0 |

### 按数据结构/算法范式分布

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

### 按语言覆盖

| 语言 | 实现题数 |
|------|----------|
| Rust | 71 |
| Python | 80 |
| Go | 60 |
| Lean (形式化证明) | 14 |

---

## 完整索引表

| 题号 | 题目名称 | 难度 | 分类 | 所属文档 | Rust | Python | Go | Lean证明 |
|------|----------|------|------|----------|------|--------|-----|----------|
| 1 | Two Sum | 简单 | 数组/哈希表 | [04-哈希表](../01-数据结构专题/04-哈希表.md) | ✓ | ✓ | ✓ | ✓ |
| 3 | Longest Substring Without Repeating Characters | 中等 | 字符串/滑动窗口 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) | ✓ | ✓ | ✓ | ✓ |
| 4 | Median of Two Sorted Arrays | 困难 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ |  |
| 5 | Longest Palindromic Substring | 中等 | 字符串/动态规划 | [02-回文问题](../04-字符串专题/02-回文问题.md) | ✓ | ✓ |  |  |
| 9 | Palindrome Number | 简单 | 数学 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 11 | Container With Most Water | 中等 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) | ✓ | ✓ | ✓ |  |
| 15 | 3Sum | 中等 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) | ✓ | ✓ | ✓ | ✓ |
| 17 | Letter Combinations of a Phone Number | 中等 | 字符串/回溯 |  | ✓ | ✓ |  |  |
| 20 | Valid Parentheses | 简单 | 栈 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 21 | Merge Two Sorted Lists | 简单 | 链表 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ | ✓ |
| 23 | Merge k Sorted Lists | 困难 | 链表/分治/堆 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ |  |
| 26 | Remove Duplicates from Sorted Array | 简单 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) | ✓ | ✓ | ✓ |  |
| 28 | Implement strStr() | 简单 | 字符串/KMP | [01-字符串匹配与KMP应用](../04-字符串专题/01-字符串匹配与KMP应用.md) | ✓ | ✓ |  |  |
| 33 | Search in Rotated Sorted Array | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ |  |
| 37 | Sudoku Solver | 困难 | 回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ |  |  |
| 39 | Combination Sum | 中等 | 数组/回溯 |  | ✓ | ✓ |  |  |
| 42 | Trapping Rain Water | 困难 | 数组/双指针/动态规划 | [01-高频Top100-数组与链表](../06-面试专题/01-高频Top100-数组与链表.md) |  |  | ✓ |  |
| 45 | Jump Game II | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 46 | Permutations | 中等 | 数组/回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ | ✓ |  |
| 48 | Rotate Image | 中等 | 数组/数学 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) | ✓ | ✓ |  |  |
| 50 | Pow(x, n) | 中等 | 数学/分治 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 51 | N-Queens | 困难 | 回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ |  |  |
| 53 | Maximum Subarray | 简单 | 数组/动态规划/分治 | [06-分治](../02-算法范式专题/06-分治.md) |  |  |  | ✓ |
| 54 | Spiral Matrix | 中等 | 数组/模拟 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) |  | ✓ |  |  |
| 55 | Jump Game | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 62 | Unique Paths | 中等 | 数组/动态规划/数学 | [02-组合数学入门](../03-数学专题/02-组合数学入门.md) | ✓ | ✓ | ✓ |  |
| 70 | Climbing Stairs | 简单 | 动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 72 | Edit Distance | 困难 | 字符串/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 76 | Minimum Window Substring | 困难 | 字符串/滑动窗口/哈希表 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) | ✓ | ✓ | ✓ |  |
| 79 | Word Search | 中等 | 数组/回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) |  |  | ✓ |  |
| 94 | Binary Tree Inorder Traversal | 简单 | 树/栈 | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 96 | Unique Binary Search Trees | 中等 | 树/动态规划/数学 | [02-组合数学入门](../03-数学专题/02-组合数学入门.md) | ✓ | ✓ | ✓ |  |
| 102 | Binary Tree Level Order Traversal | 中等 | 树/BFS | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) | ✓ | ✓ |  |  |
| 104 | Maximum Depth of Binary Tree | 简单 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ | ✓ | ✓ |
| 127 | Word Ladder | 困难 | BFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ |  |
| 133 | Clone Graph | 中等 | 图/DFS/BFS | [01-图的遍历（DFS-BFS-并查集）](../05-图论专题/01-图的遍历（DFS-BFS-并查集）.md) | ✓ | ✓ |  |  |
| 136 | Single Number | 简单 | 位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) | ✓ | ✓ |  | ✓ |
| 137 | Single Number II | 中等 | 位运算 |  |  | ✓ |  |  |
| 141 | Linked List Cycle | 简单 | 链表/双指针 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ | ✓ |
| 142 | Linked List Cycle II | 中等 | 链表/双指针/数学 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ |  |
| 153 | Find Minimum in Rotated Sorted Array | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ |  |
| 155 | Min Stack | 中等 | 栈/设计 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 167 | Two Sum II - Input Array Is Sorted | 中等 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) |  | ✓ | ✓ |  |
| 191 | Number of 1 Bits | 简单 | 位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) |  | ✓ | ✓ |  |
| 198 | House Robber | 中等 | 动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 200 | Number of Islands | 中等 | DFS/BFS/并查集 | [07-并查集](../01-数据结构专题/07-并查集.md) | ✓ | ✓ | ✓ | ✓ |
| 204 | Count Primes | 中等 | 数学/质数筛 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 206 | Reverse Linked List | 简单 | 链表 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ |  |  |
| 207 | Course Schedule | 中等 | 图/拓扑排序/DFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ | ✓ |
| 209 | Minimum Size Subarray Sum | 中等 | 数组/前缀和/滑动窗口 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) | ✓ | ✓ | ✓ |  |
| 210 | Course Schedule II | 中等 | 图/拓扑排序 | [03-拓扑排序与DAG DP](../05-图论专题/03-拓扑排序与DAG DP.md) | ✓ | ✓ |  |  |
| 214 | Shortest Palindrome | 困难 | 字符串/KMP | [01-字符串匹配与KMP应用](../04-字符串专题/01-字符串匹配与KMP应用.md) |  | ✓ |  |  |
| 223 | Rectangle Area | 中等 | 数学/几何 | [03-计算几何基础](../03-数学专题/03-计算几何基础.md) | ✓ | ✓ | ✓ |  |
| 226 | Invert Binary Tree | 简单 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 232 | Implement Queue using Stacks | 简单 | 栈/队列/设计 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 236 | Lowest Common Ancestor of a Binary Tree | 中等 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 239 | Sliding Window Maximum | 困难 | 队列/滑动窗口/单调队列 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 240 | Search a 2D Matrix II | 中等 | 数组/二分查找/分治 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) |  | ✓ | ✓ |  |
| 260 | Single Number III | 中等 | 位运算 |  |  | ✓ |  |  |
| 300 | Longest Increasing Subsequence | 中等 | 数组/二分查找/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 312 | Burst Balloons | 困难 | 数组/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 322 | Coin Change | 中等 | 动态规划 | [03-高频Top100-DP与贪心](../06-面试专题/03-高频Top100-DP与贪心.md) |  | ✓ |  |  |
| 338 | Counting Bits | 简单 | 动态规划/位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) |  | ✓ |  |  |
| 370 | Range Addition | 中等 | 数组/差分 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 372 | Super Pow | 中等 | 数学/分治/模运算 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 384 | Shuffle an Array | 中等 | 数组/随机/设计 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 398 | Random Pick Index | 中等 | 数组/随机/蓄水池抽样 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 416 | Partition Equal Subset Sum | 中等 | 动态规划/背包问题 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 435 | Non-overlapping Intervals | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 455 | Assign Cookies | 简单 | 贪心/排序 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 470 | Implement Rand10() Using Rand7() | 中等 | 数学/概率/随机 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 516 | Longest Palindromic Subsequence | 中等 | 字符串/动态规划 | [02-回文问题](../04-字符串专题/02-回文问题.md) | ✓ | ✓ | ✓ |  |
| 523 | Continuous Subarray Sum | 中等 | 数组/哈希表/数学 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 560 | Subarray Sum Equals K | 中等 | 数组/哈希表/前缀和 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 583 | Delete Operation for Two Strings | 中等 | 字符串/动态规划 | [03-字符串动态规划](../04-字符串专题/03-字符串动态规划.md) | ✓ | ✓ | ✓ |  |
| 587 | Erect the Fence | 困难 | 数学/计算几何/凸包 | [03-计算几何基础](../03-数学专题/03-计算几何基础.md) | ✓ | ✓ | ✓ |  |
| 647 | Palindromic Substrings | 中等 | 字符串/动态规划/中心扩展 | [02-回文问题](../04-字符串专题/02-回文问题.md) |  | ✓ | ✓ |  |
| 704 | Binary Search | 简单 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ | ✓ |
| 743 | Network Delay Time | 中等 | 图/Dijkstra/最短路径 | [02-最短路径（Dijkstra-Bellman-Ford-SPFA）](../05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md) | ✓ | ✓ | ✓ |  |
| 787 | Cheapest Flights Within K Stops | 中等 | 图/动态规划/最短路径 | [02-最短路径（Dijkstra-Bellman-Ford-SPFA）](../05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md) | ✓ | ✓ |  |  |
| 912 | Sort an Array | 中等 | 数组/排序/分治 | [06-分治](../02-算法范式专题/06-分治.md) | ✓ | ✓ | ✓ |  |
| 994 | Rotting Oranges | 中等 | BFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ |  |
| 1143 | Longest Common Subsequence | 中等 | 字符串/动态规划 | [03-字符串动态规划](../04-字符串专题/03-字符串动态规划.md) | ✓ | ✓ | ✓ |  |
| 1584 | Min Cost to Connect All Points | 中等 | 图/最小生成树/Prim/Kruskal | [04-最小生成树（Prim-Kruskal）](../05-图论专题/04-最小生成树（Prim-Kruskal）.md) | ✓ |  |  |  |

---

## 数据一致性审计

> 以下列出文档与代码之间的覆盖缺口，供后续补全参考。

### 仅有文档引用、无代码实现

以下题号在专题文档中被讨论或引用，但 `examples/` 下尚未找到对应代码实现：

（无）

### 仅有代码实现、无文档覆盖

以下题号在 `examples/` 下有代码实现，但在专题文档中未被明确引用：

| 题号 | 题目名称 | 代码文件 |
|------|----------|----------|
| 17 | Letter Combinations of a Phone Number | lc0017_letter_combinations.rs |
| 39 | Combination Sum | lc0039_combination_sum.rs |
| 137 | Single Number II | lc0137_single_number_ii.py |
| 260 | Single Number III | lc0260_single_number_iii.py |

### Lean 形式化证明清单

| 题号 | 题目名称 | Lean 文件 |
|------|----------|-----------|
| 1 | Two Sum | lc0001_two_sum.lean |
| 3 | Longest Substring Without Repeating Characters | lc0003_longest_substring.lean |
| 15 | 3Sum | lc0015_3sum.lean |
| 21 | Merge Two Sorted Lists | lc0021_merge_two_sorted_lists.lean |
| 53 | Maximum Subarray | lc0053_maximum_subarray.lean |
| 70 | Climbing Stairs | lc0070_climbing_stairs.lean |
| 72 | Edit Distance | lc0072_edit_distance.lean |
| 104 | Maximum Depth of Binary Tree | lc0104_maximum_depth_of_binary_tree.lean |
| 136 | Single Number | lc0136_single_number.lean |
| 141 | Linked List Cycle | lc0141_linked_list_cycle.lean |
| 198 | House Robber | lc0198_house_robber.lean |
| 200 | Number of Islands | lc0200_number_of_islands.lean |
| 207 | Course Schedule | lc0207_course_schedule.lean |
| 704 | Binary Search | lc0704_binary_search.lean |
