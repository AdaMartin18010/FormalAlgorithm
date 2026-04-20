---
title: 04-字符串算法. Rabin-Karp 算法 / Rabin-Karp Algorithm
version: 1.0
status: draft
last_updated: 2026-04-21
owner: 算法理论工作组
concepts: ["排序", "搜索", "图算法", "动态规划", "贪心"]
level: 中级
---


> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)

## 04-字符串算法. Rabin-Karp 算法 / Rabin-Karp Algorithm

### 1. 理论基础

Rabin-Karp 算法由 Karp 与 Rabin 于 1987 年提出 [Karp & Rabin, 1987]。其核心思想是将长度为 $m$ 的子串映射为一个 $b$ 进制整数，再对某个大素数 $q$ 取模，从而把字符串比较转化为**滚动哈希**（Rolling Hash）值的比较。通过模运算的代数性质，相邻窗口的哈希值可在 $O(1)$ 时间内递推更新。

给定字符串 $S$ 与基数 $b$、模数 $q$，子串 $S[i..i+m-1]$ 的哈希值为

$$
h(i) \;=\; \Bigl(\sum_{j=0}^{m-1} S[i+j] \cdot b^{m-1-j}\Bigr) \bmod q .
$$

相邻窗口满足

$$
h(i+1) \;=\; \bigl[\,h(i) \cdot b - S[i] \cdot b^{m} + S[i+m] \,\bigr] \bmod q .
$$

（具体实现中常采用正向累加并配合最高位幂次调整，等价于上述递推。）

### 2. 算法设计

1. **初始化**：
   - 计算模式串 $P$ 的哈希值 $h_P$；
   - 预计算 $b^{m-1} \bmod q$；
   - 计算文本首窗口 $T[0..m-1]$ 的哈希值 $h_0$。

2. **滑动窗口**：
   - 对 $i = 0 \dots n-m$，比较 $h_i$ 与 $h_P$；
   - 若哈希相等，执行**逐字符校验**以排除伪命中（spurious hit）；
   - 使用滚动公式在 $O(1)$ 时间内计算 $h_{i+1}$。

3. **扩展功能**：项目实现还支持：
   - `search_multiple`：多模式同时检索；
   - `similarity`：基于 k-gram 指纹的 Jaccard 相似度，用于抄袭检测；
   - `RabinKarp2D`：二维矩阵模式匹配的框架。

**代码实现**：[`rabin_karp.rs`](../../../examples/algorithms/src/rabin_karp.rs)

### 3. 复杂度分析

| 场景 | 时间复杂度 | 空间复杂度 | 说明 |
|------|-----------|-----------|------|
| 平均情况 | $O(n+m)$ | $O(1)$ | 哈希冲突概率极低 |
| 最坏情况 | $O(n \cdot m)$ | $O(1)$ | 所有窗口均发生哈希冲突 |
| 多模式匹配 | $O(k \cdot (n+m))$ | $O(k)$ | $k$ 为模式串数量 |

其中 $n$ 为文本长度，$m$ 为模式长度。实际应用中，选取足够大的随机素数 $q$ 可使冲突概率趋近于 $1/q$。

### 4. 形式化验证 / 正确性论证

**引理（滚动哈希等价性）**：对任意 $i \in [0, n-m)$，算法递推计算出的 $h(i+1)$ 等于子串 $T[i+1..i+m]$ 的直接哈希值。

*证明*：由定义

$$
\begin{aligned}
h(i+1) &\equiv h(i) \cdot b - T[i] \cdot b^{m} + T[i+m] \pmod q \\
&\equiv \Bigl(\sum_{j=0}^{m-1} T[i+j] b^{m-j}\Bigr) - T[i] b^{m} + T[i+m] \pmod q \\
&\equiv \sum_{j=1}^{m-1} T[i+j] b^{m-j} + T[i+m] \pmod q \\
&\equiv \sum_{j=0}^{m-1} T[i+1+j] b^{m-1-j} \pmod q,
\end{aligned}
$$

恰为下一窗口的哈希定义。$\square$

**定理（Rabin-Karp 正确性）**：若 $h(i) = h_P$ 且逐字符校验通过，则 $T[i..i+m-1] = P$；反之若两者相等，则必有 $h(i) = h_P$。

*证明*：直接由哈希函数的定义与同余关系的等价性可得。逐字符校验排除了哈希冲突导致的伪命中。$\square$

### 5. 应用场景

- **多模式同时检索**：在日志分析、病毒特征码扫描中一次性搜索大量短模式。
- **抄袭检测**：将文档切分为 k-gram，计算指纹集合的 Jaccard 相似度 [Schleimer et al., 2003]。
- **DNA 序列比对**：利用基数 $b=4$ 对碱基 {A,T,C,G} 编码，实现快速子串筛选。
- **二维图像匹配**：`RabinKarp2D` 可扩展为双重滚动哈希，用于图像模板搜索。

### 6. 扩展变体

| 变体 | 核心思想 | 效果 |
|------|----------|------|
| **双哈希** | 使用两个独立的 $(b,q)$ 对计算哈希对 | 将冲突概率降至 $O(1/q^2)$ |
| **Rabin-Karp 2D** | 先对行做滚动哈希，再对列做滚动哈希 | 实现 $O(n^2)$ 的二维模式匹配 |
| **多项式滚动哈希** | 采用随机基数并配合模 $2^{64}$（自然溢出） | 利用 CPU 字长优势，常数因子极小 |
| **k-gram 指纹** | 提取所有长度为 $k$ 的子串指纹 | 用于局部敏感哈希（LSH）与文档去重 |

### 参考文献

1. **R. M. Karp, M. O. Rabin**, "Efficient Randomized Pattern-Matching Algorithms", *IBM Journal of Research and Development*, 31(2), 1987.
2. **S. Schleimer, D. S. Wilkerson, A. Aiken**, "Winnowing: Local Algorithms for Document Fingerprinting", *SIGMOD*, 2003.
3. **T. H. Cormen et al.**, *Introduction to Algorithms*, 3rd ed., MIT Press, 2009.
---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解Rabin-Karp算法的核心概念
- 掌握Rabin-Karp算法的形式化表示
