---
title: 04-字符串算法. Manacher 算法 / Manacher's Algorithm
version: 1.0
status: draft
last_updated: 2026-04-21
owner: 算法理论工作组
concepts: ["排序", "搜索", "图算法", "动态规划", "贪心"]
level: 中级
---


> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)

## 04-字符串算法. Manacher 算法 / Manacher's Algorithm

### 1. 理论基础

Manacher 算法由 Manacher 于 1975 年提出 [Manacher, 1975]，用于在 $O(n)$ 时间内求解字符串的最长回文子串问题。其核心洞察是：

1. 通过**插入虚拟分隔符**（如 `#`），将原字符串的奇数长度回文与偶数长度回文统一为以某个中心向两侧扩展的**奇数长度回文**；
2. 维护当前最右回文的中心 $C$ 与右边界 $R$，利用回文的对称性复用已计算信息，避免大量冗余的中心扩展。

### 2. 算法设计

1. **构造辅助串**：对原串 $S = s_1 s_2 \dots s_n$，构造
   $$
   T \;=\; \#s_1\#s_2\#\dots\#s_n\#,
   $$
   长度 $m = 2n+1$。$T$ 中的任意回文均对应 $S$ 中的某个回文。

2. **计算回文半径数组 $P$**：$P[i]$ 表示以 $T[i]$ 为中心，向单侧扩展的字符数（即回文半径）。
   - 维护当前最右回文的中心 $C$ 和右边界 $R = C + P[C]$；
   - 对 $i = 0 \dots m-1$：
     - 若 $i < R$，令镜像位置 $mirror = 2C - i$，则 $P[i] \ge \min(P[mirror],\; R-i)$；
     - 以 $i$ 为中心向两侧暴力扩展，更新 $P[i]$；
     - 若 $i + P[i] > R$，更新 $C = i$，$R = i + P[i]$。

3. **结果提取**：
   - 最长回文半径 $\max(P)$ 对应原串中的最长回文子串长度为 $\max(P)$；
   - 起始位置为 $(center - \max(P)) / 2$。

项目实现 additionally 提供了 `count_palindromes` 接口，用于统计所有回文子串的数量。

**代码实现**：[`manacher.rs`](../../../examples/algorithms/src/manacher.rs)

### 3. 复杂度分析

| 操作 | 时间复杂度 | 空间复杂度 |
|------|-----------|-----------|
| 构造辅助串 | $O(n)$ | $O(n)$ |
| 计算回文半径 | $O(n)$ | $O(n)$ |
| 提取最长回文 | $O(n)$ | $O(1)$ 额外 |
| **总计** | **$O(n)$** | **$O(n)$** |

其中 $n$ 为原字符串长度。暴力中心扩展的 $O(n^2)$ 算法在此处被优化至线性，关键在于右边界 $R$ 的单调递增。

### 4. 形式化验证 / 正确性论证

**引理（对称性复用）**：设当前最右回文区间为 $[C-P[C],\; C+P[C]]$，对任意 $i \in [C, R]$，其镜像 $mirror = 2C - i$ 满足：

$$
P[i] \;=\; \min\bigl(P[mirror],\; R-i\bigr) + \text{ext},
$$

其中 $\text{ext}$ 为在 $R$ 右侧的额外扩展长度。

*证明*：由于 $[C-P[C], C+P[C]]$ 是回文，$T[i-k..i+k]$ 与 $T[mirror-k..mirror+k]$ 关于 $C$ 对称。当 $k \le \min(P[mirror], R-i)$ 时，两侧均落在已知回文区间内，必然相等。若 $P[mirror] > R-i$，则以 $i$ 为中心的回文右边界至少到达 $R$，但 $R$ 之外无法由对称性保证，需暴力比较。$\square$

**定理（Manacher 线性时间）**：算法计算整个 $P$ 数组的比较次数不超过 $2m$。

*证明*：右边界 $R$ 在算法执行过程中只增不减。每次进入中心扩展循环时，要么 $i \ge R$（此时 $R$ 至少扩展到 $i+P[i]$），要么 $i < R$ 但只需从 $R+1$ 开始继续比较。因此每成功比较一次，$R$ 至少右移一位。由于 $R \le m-1$，总比较次数为 $O(m) = O(n)$。$\square$

### 5. 应用场景

- **生物信息学**：DNA 回文序列检测，如限制性内切酶的识别位点（palindromic recognition sites）。
- **文本编辑**：实时高亮或提取文档中的最长对称短语、诗句。
- **分子生物学**：RNA 二级结构中的茎环结构（stem-loop）常表现为近似回文。
- **数据压缩**：某些基于回文的压缩编码需要快速枚举或定位最长回文。

### 6. 扩展变体

| 变体 | 核心思想 | 应用场景 |
|------|----------|----------|
| **在线 Manacher** | 逐字符接收输入并增量维护 $[C, R]$ | 流式文本中的实时回文检测 |
| **回文树（Eertree）** | 识别所有不同回文子串的最小树形结构，支持在线插入 | 回文子串计数、动态回文查询 |
| **近似回文匹配** | 允许 $k$ 个错配的编辑距离扩展 | 生物序列中的退化回文识别 |
| **二维 Manacher** | 将行/列分别做 Manacher，再结合动态规划 | 矩阵中寻找最长二维回文 |

### 参考文献

1. **G. Manacher**, "A New Linear-Time On-Line Algorithm for Finding the Smallest Initial Palindrome of a String", *Journal of the ACM*, 22(3), 1975.
2. **M. Rubinchik, A. M. Shur**, "Eertree: An Efficient Data Structure for Processing Palindromes in Strings", *European Journal of Combinatorics*, 68, 2018.
3. **D. Gusfield**, *Algorithms on Strings, Trees, and Sequences*, Cambridge University Press, 1997.
---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解Manacher算法的核心概念
- 掌握Manacher算法的形式化表示
