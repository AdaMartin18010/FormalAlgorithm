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
| 索引题号总数 | 147 |
| 有代码实现 | 83 |
| 有文档覆盖 | 143 |
| 代码+文档完全覆盖 | 79 |
| 有形式化证明 (Lean) | 14 |

### 按难度分布

| 难度 | 数量 |
|------|------|
| 简单 | 28 |
| 中等 | 94 |
| 困难 | 25 |
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
| 19 | Remove Nth Node From End of List | 中等 | 链表/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) |  |  |  | |
| 20 | Valid Parentheses | 简单 | 栈 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 21 | Merge Two Sorted Lists | 简单 | 链表 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ | ✓ |
| 23 | Merge k Sorted Lists | 困难 | 链表/分治/堆 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ |  |
| 26 | Remove Duplicates from Sorted Array | 简单 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) | ✓ | ✓ | ✓ |  |
| 28 | Implement strStr() | 简单 | 字符串/KMP | [01-字符串匹配与KMP应用](../04-字符串专题/01-字符串匹配与KMP应用.md) | ✓ | ✓ |  |  |
| 33 | Search in Rotated Sorted Array | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ |  |
| 34 | Find First and Last Position of Element in Sorted Array | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) |  |  |  | |
| 35 | Search Insert Position | 简单 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) |  |  |  | |
| 37 | Sudoku Solver | 困难 | 回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ |  |  |
| 39 | Combination Sum | 中等 | 数组/回溯 |  | ✓ | ✓ |  |  |
| 42 | Trapping Rain Water | 困难 | 数组/双指针/动态规划 | [01-高频Top100-数组与链表](../06-面试专题/01-高频Top100-数组与链表.md) |  |  | ✓ |  |
| 45 | Jump Game II | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 46 | Permutations | 中等 | 数组/回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ | ✓ |  |
| 48 | Rotate Image | 中等 | 数组/数学 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) | ✓ | ✓ |  |  |
| 49 | Group Anagrams | 中等 | 字符串/哈希表 | [04-哈希表](../01-数据结构专题/04-哈希表.md) |  |  |  | |
| 50 | Pow(x, n) | 中等 | 数学/分治 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 51 | N-Queens | 困难 | 回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) | ✓ | ✓ |  |  |
| 53 | Maximum Subarray | 简单 | 数组/动态规划/分治 | [06-分治](../02-算法范式专题/06-分治.md) |  |  |  | ✓ |
| 54 | Spiral Matrix | 中等 | 数组/模拟 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) |  | ✓ |  |  |
| 55 | Jump Game | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 56 | Merge Intervals | 中等 | 数组/贪心/排序 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 57 | Insert Interval | 中等 | 数组/贪心/排序 | [01-高频Top100-数组与链表](../06-面试专题/01-高频Top100-数组与链表.md) |  |  |  | |
| 62 | Unique Paths | 中等 | 数组/动态规划/数学 | [02-组合数学入门](../03-数学专题/02-组合数学入门.md) | ✓ | ✓ | ✓ |  |
| 70 | Climbing Stairs | 简单 | 动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 72 | Edit Distance | 困难 | 字符串/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 73 | Set Matrix Zeroes | 中等 | 数组/矩阵 | [01-高频Top100-数组与链表](../06-面试专题/01-高频Top100-数组与链表.md) |  |  |  | |
| 74 | Search a 2D Matrix | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) |  |  |  | |
| 76 | Minimum Window Substring | 困难 | 字符串/滑动窗口/哈希表 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) | ✓ | ✓ | ✓ |  |
| 77 | Combinations | 中等 | 数组/回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) |  |  |  | |
| 78 | Subsets | 中等 | 数组/回溯 | [00-算法范式导论](../02-算法范式专题/00-算法范式导论.md) |  |  |  | |
| 79 | Word Search | 中等 | 数组/回溯 | [09-回溯与DFS](../02-算法范式专题/09-回溯与DFS.md) |  |  | ✓ |  |
| 88 | Merge Sorted Array | 简单 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) |  |  |  | |
| 94 | Binary Tree Inorder Traversal | 简单 | 树/栈 | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 96 | Unique Binary Search Trees | 中等 | 树/动态规划/数学 | [02-组合数学入门](../03-数学专题/02-组合数学入门.md) | ✓ | ✓ | ✓ |  |
| 98 | Validate Binary Search Tree | 中等 | 树/BST/DFS | [00-数据结构专题导论](../01-数据结构专题/00-数据结构专题导论.md) |  |  |  | |
| 102 | Binary Tree Level Order Traversal | 中等 | 树/BFS | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) | ✓ | ✓ |  |  |
| 104 | Maximum Depth of Binary Tree | 简单 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ | ✓ | ✓ |
| 122 | Best Time to Buy and Sell Stock II | 中等 | 数组/贪心/动态规划 | [00-算法范式导论](../02-算法范式专题/00-算法范式导论.md) |  |  |  | |
| 124 | Binary Tree Maximum Path Sum | 困难 | 树/DFS/动态规划 | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) |  |  |  | |
| 125 | Valid Palindrome | 简单 | 字符串/双指针 | [00-算法范式导论](../02-算法范式专题/00-算法范式导论.md) |  |  |  | |
| 127 | Word Ladder | 困难 | BFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ |  |
| 128 | Longest Consecutive Sequence | 中等 | 数组/哈希表/并查集 | [04-哈希表](../01-数据结构专题/04-哈希表.md) |  |  |  | |
| 133 | Clone Graph | 中等 | 图/DFS/BFS | [01-图的遍历（DFS-BFS-并查集）](../05-图论专题/01-图的遍历（DFS-BFS-并查集）.md) | ✓ | ✓ |  |  |
| 134 | Gas Station | 中等 | 数组/贪心 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 136 | Single Number | 简单 | 位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) | ✓ | ✓ |  | ✓ |
| 137 | Single Number II | 中等 | 位运算 |  |  | ✓ |  |  |
| 141 | Linked List Cycle | 简单 | 链表/双指针 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ | ✓ |
| 142 | Linked List Cycle II | 中等 | 链表/双指针/数学 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ | ✓ |  |
| 146 | LRU Cache | 中等 | 设计/哈希表/双向链表 | [04-哈希表](../01-数据结构专题/04-哈希表.md) |  |  |  | |
| 148 | Sort List | 中等 | 链表/分治/排序 | [06-分治](../02-算法范式专题/06-分治.md) |  |  |  | |
| 153 | Find Minimum in Rotated Sorted Array | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ |  |
| 155 | Min Stack | 中等 | 栈/设计 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 162 | Find Peak Element | 中等 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) |  |  |  | |
| 167 | Two Sum II - Input Array Is Sorted | 中等 | 数组/双指针 | [02-双指针](../02-算法范式专题/02-双指针.md) |  | ✓ | ✓ |  |
| 191 | Number of 1 Bits | 简单 | 位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) |  | ✓ | ✓ |  |
| 198 | House Robber | 中等 | 动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ | ✓ |
| 200 | Number of Islands | 中等 | DFS/BFS/并查集 | [07-并查集](../01-数据结构专题/07-并查集.md) | ✓ | ✓ | ✓ | ✓ |
| 204 | Count Primes | 中等 | 数学/质数筛 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 206 | Reverse Linked List | 简单 | 链表 | [02-链表](../01-数据结构专题/02-链表.md) | ✓ | ✓ |  |  |
| 207 | Course Schedule | 中等 | 图/拓扑排序/DFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ | ✓ |
| 208 | Implement Trie (Prefix Tree) | 中等 | 设计/Trie树 | [08-Trie树](../01-数据结构专题/08-Trie树.md) |  |  |  | |
| 209 | Minimum Size Subarray Sum | 中等 | 数组/前缀和/滑动窗口 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) | ✓ | ✓ | ✓ |  |
| 210 | Course Schedule II | 中等 | 图/拓扑排序 | [03-拓扑排序与DAG DP](../05-图论专题/03-拓扑排序与DAG DP.md) | ✓ | ✓ |  |  |
| 212 | Word Search II | 困难 | 数组/回溯/Trie树 | [08-Trie树](../01-数据结构专题/08-Trie树.md) |  |  |  | |
| 214 | Shortest Palindrome | 困难 | 字符串/KMP | [01-字符串匹配与KMP应用](../04-字符串专题/01-字符串匹配与KMP应用.md) |  | ✓ |  |  |
| 215 | Kth Largest Element in an Array | 中等 | 数组/分治/快速选择/堆 | [06-堆与优先队列](../01-数据结构专题/06-堆与优先队列.md) |  |  |  | |
| 223 | Rectangle Area | 中等 | 数学/几何 | [03-计算几何基础](../03-数学专题/03-计算几何基础.md) | ✓ | ✓ | ✓ |  |
| 224 | Basic Calculator | 困难 | 字符串/栈/数学 | [05-大厂真题分类（字节-阿里-腾讯-Google）](../06-面试专题/05-大厂真题分类（字节-阿里-腾讯-Google）.md) |  |  |  | |
| 226 | Invert Binary Tree | 简单 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 232 | Implement Queue using Stacks | 简单 | 栈/队列/设计 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 235 | Lowest Common Ancestor of a Binary Search Tree | 简单 | 树/BST/DFS | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) |  |  |  | |
| 236 | Lowest Common Ancestor of a Binary Tree | 中等 | 树/DFS | [05-二叉树与BST](../01-数据结构专题/05-二叉树与BST.md) | ✓ | ✓ |  |  |
| 238 | Product of Array Except Self | 中等 | 数组/前缀和 | [01-高频Top100-数组与链表](../06-面试专题/01-高频Top100-数组与链表.md) |  |  |  | |
| 239 | Sliding Window Maximum | 困难 | 队列/滑动窗口/单调队列 | [03-栈与队列](../01-数据结构专题/03-栈与队列.md) | ✓ | ✓ | ✓ |  |
| 240 | Search a 2D Matrix II | 中等 | 数组/二分查找/分治 | [01-数组与矩阵](../01-数据结构专题/01-数组与矩阵.md) |  | ✓ | ✓ |  |
| 253 | Meeting Rooms II | 中等 | 数组/贪心/排序/堆 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 260 | Single Number III | 中等 | 位运算 |  |  | ✓ |  |  |
| 261 | Graph Valid Tree | 中等 | 图/DFS/BFS/并查集 | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) |  |  |  | |
| 269 | Alien Dictionary | 困难 | 图/拓扑排序 | [00-图论专题导论](../05-图论专题/00-图论专题导论.md) |  |  |  | |
| 287 | Find the Duplicate Number | 中等 | 数组/双指针/二分查找 | [02-双指针](../02-算法范式专题/02-双指针.md) |  |  |  | |
| 289 | Game of Life | 中等 | 数组/矩阵/模拟 | [01-枚举与模拟](../02-算法范式专题/01-枚举与模拟.md) |  |  |  | |
| 295 | Find Median from Data Stream | 困难 | 设计/堆/数据流 | [06-堆与优先队列](../01-数据结构专题/06-堆与优先队列.md) |  |  |  | |
| 297 | Serialize and Deserialize Binary Tree | 困难 | 树/设计/DFS/BFS | [02-高频Top100-树与图](../06-面试专题/02-高频Top100-树与图.md) |  |  |  | |
| 300 | Longest Increasing Subsequence | 中等 | 数组/二分查找/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 303 | Range Sum Query - Immutable | 简单 | 数组/前缀和/设计 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) |  |  |  | |
| 304 | Range Sum Query 2D - Immutable | 中等 | 数组/矩阵/前缀和/设计 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) |  |  |  | |
| 312 | Burst Balloons | 困难 | 数组/动态规划 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 315 | Count of Smaller Numbers After Self | 困难 | 数组/分治/树状数组/线段树 | [06-分治](../02-算法范式专题/06-分治.md) |  |  |  | |
| 322 | Coin Change | 中等 | 动态规划 | [03-高频Top100-DP与贪心](../06-面试专题/03-高频Top100-DP与贪心.md) |  | ✓ |  |  |
| 327 | Count of Range Sum | 困难 | 数组/分治/树状数组/线段树/排序 | [00-算法范式导论](../02-算法范式专题/00-算法范式导论.md) |  |  |  | |
| 329 | Longest Increasing Path in a Matrix | 困难 | 数组/DFS/动态规划/记忆化搜索/拓扑排序 | [03-拓扑排序与DAG DP](../05-图论专题/03-拓扑排序与DAG DP.md) |  |  |  | |
| 337 | House Robber III | 中等 | 树/DFS/动态规划 | [03-高频Top100-DP与贪心](../06-面试专题/03-高频Top100-DP与贪心.md) |  |  |  | |
| 338 | Counting Bits | 简单 | 动态规划/位运算 | [11-位运算](../02-算法范式专题/11-位运算.md) |  | ✓ |  |  |
| 344 | Reverse String | 简单 | 字符串/双指针/递归 | [02-双指针](../02-算法范式专题/02-双指针.md) |  |  |  | |
| 370 | Range Addition | 中等 | 数组/差分 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 372 | Super Pow | 中等 | 数学/分治/模运算 | [01-数论基础（GCD-LCM-质数）](../03-数学专题/01-数论基础（GCD-LCM-质数）.md) | ✓ | ✓ | ✓ |  |
| 378 | Kth Smallest Element in a Sorted Matrix | 中等 | 数组/二分查找/堆/排序 | [05-二分查找](../02-算法范式专题/05-二分查找.md) |  |  |  | |
| 384 | Shuffle an Array | 中等 | 数组/随机/设计 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 398 | Random Pick Index | 中等 | 数组/随机/蓄水池抽样 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 406 | Queue Reconstruction by Height | 中等 | 数组/贪心/排序 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 416 | Partition Equal Subset Sum | 中等 | 动态规划/背包问题 | [08-动态规划](../02-算法范式专题/08-动态规划.md) | ✓ | ✓ | ✓ |  |
| 424 | Longest Repeating Character Replacement | 中等 | 字符串/滑动窗口 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 432 | All O'one Data Structure | 困难 | 设计/哈希表/链表 | [00-数据结构专题导论](../01-数据结构专题/00-数据结构专题导论.md) |  |  |  | |
| 435 | Non-overlapping Intervals | 中等 | 数组/贪心/动态规划 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 438 | Find All Anagrams in a String | 中等 | 字符串/滑动窗口/哈希表 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 452 | Minimum Number of Arrows to Burst Balloons | 中等 | 数组/贪心/排序 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 455 | Assign Cookies | 简单 | 贪心/排序 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) | ✓ | ✓ | ✓ |  |
| 459 | Repeated Substring Pattern | 简单 | 字符串/KMP/枚举 | [00-字符串专题导论](../04-字符串专题/00-字符串专题导论.md) |  |  |  | |
| 470 | Implement Rand10() Using Rand7() | 中等 | 数学/概率/随机 | [04-概率与随机算法面试题](../03-数学专题/04-概率与随机算法面试题.md) | ✓ | ✓ | ✓ |  |
| 480 | Sliding Window Median | 困难 | 数组/滑动窗口/有序集合/堆 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 494 | Target Sum | 中等 | 数组/动态规划/回溯 | [03-高频Top100-DP与贪心](../06-面试专题/03-高频Top100-DP与贪心.md) |  |  |  | |
| 516 | Longest Palindromic Subsequence | 中等 | 字符串/动态规划 | [02-回文问题](../04-字符串专题/02-回文问题.md) | ✓ | ✓ | ✓ |  |
| 523 | Continuous Subarray Sum | 中等 | 数组/哈希表/数学 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 525 | Contiguous Array | 中等 | 数组/哈希表/前缀和 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) |  |  |  | |
| 547 | Number of Provinces | 中等 | 图/DFS/BFS/并查集 | [07-并查集](../01-数据结构专题/07-并查集.md) |  |  |  | |
| 560 | Subarray Sum Equals K | 中等 | 数组/哈希表/前缀和 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) | ✓ | ✓ | ✓ |  |
| 567 | Permutation in String | 中等 | 字符串/滑动窗口/哈希表/双指针 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 583 | Delete Operation for Two Strings | 中等 | 字符串/动态规划 | [03-字符串动态规划](../04-字符串专题/03-字符串动态规划.md) | ✓ | ✓ | ✓ |  |
| 587 | Erect the Fence | 困难 | 数学/计算几何/凸包 | [03-计算几何基础](../03-数学专题/03-计算几何基础.md) | ✓ | ✓ | ✓ |  |
| 621 | Task Scheduler | 中等 | 数组/贪心/排序/堆 | [07-贪心算法](../02-算法范式专题/07-贪心算法.md) |  |  |  | |
| 643 | Maximum Average Subarray I | 简单 | 数组/滑动窗口/前缀和 | [00-算法范式导论](../02-算法范式专题/00-算法范式导论.md) |  |  |  | |
| 647 | Palindromic Substrings | 中等 | 字符串/动态规划/中心扩展 | [02-回文问题](../04-字符串专题/02-回文问题.md) |  | ✓ | ✓ |  |
| 648 | Replace Words | 中等 | 字符串/Trie树 | [08-Trie树](../01-数据结构专题/08-Trie树.md) |  |  |  | |
| 704 | Binary Search | 简单 | 数组/二分查找 | [05-二分查找](../02-算法范式专题/05-二分查找.md) | ✓ | ✓ | ✓ | ✓ |
| 743 | Network Delay Time | 中等 | 图/Dijkstra/最短路径 | [02-最短路径（Dijkstra-Bellman-Ford-SPFA）](../05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md) | ✓ | ✓ | ✓ |  |
| 787 | Cheapest Flights Within K Stops | 中等 | 图/动态规划/最短路径 | [02-最短路径（Dijkstra-Bellman-Ford-SPFA）](../05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md) | ✓ | ✓ |  |  |
| 862 | Shortest Subarray with Sum at Least K | 困难 | 数组/前缀和/单调队列/滑动窗口 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 912 | Sort an Array | 中等 | 数组/排序/分治 | [06-分治](../02-算法范式专题/06-分治.md) | ✓ | ✓ | ✓ |  |
| 994 | Rotting Oranges | 中等 | BFS | [10-BFS与图搜索](../02-算法范式专题/10-BFS与图搜索.md) | ✓ | ✓ | ✓ |  |
| 1004 | Max Consecutive Ones III | 中等 | 数组/滑动窗口/双指针 | [03-滑动窗口](../02-算法范式专题/03-滑动窗口.md) |  |  |  | |
| 1044 | Longest Duplicate Substring | 困难 | 字符串/二分查找/Rabin-Karp/后缀数组 | [00-字符串专题导论](../04-字符串专题/00-字符串专题导论.md) |  |  |  | |
| 1099 | Two Sum Less Than K | 简单 | 数组/双指针/排序 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) |  |  |  | |
| 1109 | Corporate Flight Bookings | 中等 | 数组/差分/前缀和 | [04-前缀和与差分](../02-算法范式专题/04-前缀和与差分.md) |  |  |  | |
| 1135 | Connecting Cities With Minimum Cost | 中等 | 图/最小生成树/Kruskal/Prim | [00-图论专题导论](../05-图论专题/00-图论专题导论.md) |  |  |  | |
| 1143 | Longest Common Subsequence | 中等 | 字符串/动态规划 | [03-字符串动态规划](../04-字符串专题/03-字符串动态规划.md) | ✓ | ✓ | ✓ |  |
| 1584 | Min Cost to Connect All Points | 中等 | 图/最小生成树/Prim/Kruskal | [04-最小生成树（Prim-Kruskal）](../05-图论专题/04-最小生成树（Prim-Kruskal）.md) | ✓ |  |  |  |
| 1631 | Path With Minimum Effort | 中等 | 图/最短路径/Dijkstra/并查集/二分查找 | [02-最短路径（Dijkstra-Bellman-Ford-SPFA）](../05-图论专题/02-最短路径（Dijkstra-Bellman-Ford-SPFA）.md) |  |  |  | |
| 1986 | Minimum Number of Work Sessions to Finish the Tasks | 中等 | 数组/动态规划/状态压缩/回溯/贪心 | [03-高频Top100-DP与贪心](../06-面试专题/03-高频Top100-DP与贪心.md) |  |  |  | |

---

## 数据一致性审计

> 以下列出文档与代码之间的覆盖缺口，供后续补全参考。

### 仅有文档引用、无代码实现

以下题号在专题文档中被讨论或引用，但 `examples/` 下尚未找到对应代码实现：

| 题号 | 题目名称 | 分类 |
|------|----------|------|
| 19 | Remove Nth Node From End of List | 链表/双指针 |
| 34 | Find First and Last Position of Element in Sorted Array | 数组/二分查找 |
| 35 | Search Insert Position | 数组/二分查找 |
| 49 | Group Anagrams | 字符串/哈希表 |
| 56 | Merge Intervals | 数组/贪心/排序 |
| 57 | Insert Interval | 数组/贪心/排序 |
| 73 | Set Matrix Zeroes | 数组/矩阵 |
| 74 | Search a 2D Matrix | 数组/二分查找 |
| 77 | Combinations | 数组/回溯 |
| 78 | Subsets | 数组/回溯 |
| 88 | Merge Sorted Array | 数组/双指针 |
| 98 | Validate Binary Search Tree | 树/BST/DFS |
| 122 | Best Time to Buy and Sell Stock II | 数组/贪心/动态规划 |
| 124 | Binary Tree Maximum Path Sum | 树/DFS/动态规划 |
| 125 | Valid Palindrome | 字符串/双指针 |
| 128 | Longest Consecutive Sequence | 数组/哈希表/并查集 |
| 134 | Gas Station | 数组/贪心 |
| 146 | LRU Cache | 设计/哈希表/双向链表 |
| 148 | Sort List | 链表/分治/排序 |
| 162 | Find Peak Element | 数组/二分查找 |
| 208 | Implement Trie (Prefix Tree) | 设计/Trie树 |
| 212 | Word Search II | 数组/回溯/Trie树 |
| 215 | Kth Largest Element in an Array | 数组/分治/快速选择/堆 |
| 224 | Basic Calculator | 字符串/栈/数学 |
| 235 | Lowest Common Ancestor of a Binary Search Tree | 树/BST/DFS |
| 238 | Product of Array Except Self | 数组/前缀和 |
| 253 | Meeting Rooms II | 数组/贪心/排序/堆 |
| 261 | Graph Valid Tree | 图/DFS/BFS/并查集 |
| 269 | Alien Dictionary | 图/拓扑排序 |
| 287 | Find the Duplicate Number | 数组/双指针/二分查找 |
| 289 | Game of Life | 数组/矩阵/模拟 |
| 295 | Find Median from Data Stream | 设计/堆/数据流 |
| 297 | Serialize and Deserialize Binary Tree | 树/设计/DFS/BFS |
| 303 | Range Sum Query - Immutable | 数组/前缀和/设计 |
| 304 | Range Sum Query 2D - Immutable | 数组/矩阵/前缀和/设计 |
| 315 | Count of Smaller Numbers After Self | 数组/分治/树状数组/线段树 |
| 327 | Count of Range Sum | 数组/分治/树状数组/线段树/排序 |
| 329 | Longest Increasing Path in a Matrix | 数组/DFS/动态规划/记忆化搜索/拓扑排序 |
| 337 | House Robber III | 树/DFS/动态规划 |
| 344 | Reverse String | 字符串/双指针/递归 |
| 378 | Kth Smallest Element in a Sorted Matrix | 数组/二分查找/堆/排序 |
| 406 | Queue Reconstruction by Height | 数组/贪心/排序 |
| 424 | Longest Repeating Character Replacement | 字符串/滑动窗口 |
| 432 | All O'one Data Structure | 设计/哈希表/链表 |
| 438 | Find All Anagrams in a String | 字符串/滑动窗口/哈希表 |
| 452 | Minimum Number of Arrows to Burst Balloons | 数组/贪心/排序 |
| 459 | Repeated Substring Pattern | 字符串/KMP/枚举 |
| 480 | Sliding Window Median | 数组/滑动窗口/有序集合/堆 |
| 494 | Target Sum | 数组/动态规划/回溯 |
| 525 | Contiguous Array | 数组/哈希表/前缀和 |
| 547 | Number of Provinces | 图/DFS/BFS/并查集 |
| 567 | Permutation in String | 字符串/滑动窗口/哈希表/双指针 |
| 621 | Task Scheduler | 数组/贪心/排序/堆 |
| 643 | Maximum Average Subarray I | 数组/滑动窗口/前缀和 |
| 648 | Replace Words | 字符串/Trie树 |
| 862 | Shortest Subarray with Sum at Least K | 数组/前缀和/单调队列/滑动窗口 |
| 1004 | Max Consecutive Ones III | 数组/滑动窗口/双指针 |
| 1044 | Longest Duplicate Substring | 字符串/二分查找/Rabin-Karp/后缀数组 |
| 1099 | Two Sum Less Than K | 数组/双指针/排序 |
| 1109 | Corporate Flight Bookings | 数组/差分/前缀和 |
| 1135 | Connecting Cities With Minimum Cost | 图/最小生成树/Kruskal/Prim |
| 1631 | Path With Minimum Effort | 图/最短路径/Dijkstra/并查集/二分查找 |
| 1986 | Minimum Number of Work Sessions to Finish the Tasks | 数组/动态规划/状态压缩/回溯/贪心 |

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
