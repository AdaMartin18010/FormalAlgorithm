---
title: 04-字符串算法. 后缀数组与 LCP / Suffix Array and LCP
version: 1.0
status: draft
last_updated: 2026-04-15
owner: 算法理论工作组
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../../项目全面梳理-2025.md)

## 04-字符串算法. 后缀数组与 LCP / Suffix Array and LCP

### 1. 理论基础

**后缀数组**（Suffix Array, SA）是字符串 $S$ 的所有后缀按字典序排序后，记录各后缀起始位置的整数数组 [Manber & Myers, 1993]。设 $|S| = n$，则

$$
SA[i] \;=\; \text{排名第 } i \text{ 的后缀在 } S \text{ 中的起始位置}.
$$

**LCP 数组**（Longest Common Prefix）记录 SA 中相邻后缀的最长公共前缀长度：

$$
LCP[i] \;=\; \text{lcp}\bigl( S[SA[i]..],\; S[SA[i-1]..] \bigr),\quad LCP[0] = 0.
$$

后缀数组与 LCP 数组共同构成字符串的**紧凑索引**，可替代功能更强但空间开销更大的后缀树。

### 2. 算法设计

#### 2.1 倍增法构建后缀数组

1. **初始化**：按首字符排序得到初始 $SA$，$rank[i]$ 为 $S[i]$ 的字符编码。
2. **倍增迭代**：设当前已按长度为 $k$ 的前缀排序，下一步以二元组 $(rank[i],\; rank[i+k])$ 为关键字重新排序。使用整数排序（如计数排序或 `sort_by`），复杂度 $O(n \log n)$。
3. **终止条件**：所有后缀的 $rank$ 互不相同，或 $k \ge n$。

#### 2.2 Kasai 算法计算 LCP

利用排名数组 $rank$（$rank[p]$ 表示后缀 $S[p..]$ 的排名）与**相邻 LCP 的递减性**：

> 若 $rank[i] > 0$，则 $LCP[rank[i]] \ge LCP[rank[i-1]] - 1$。

算法按 $i = 0 \dots n-1$ 顺序扫描，维护当前匹配长度 $k$：

- 令 $j = SA[rank[i]-1]$；
- 从 $k$ 开始比较 $S[i+k]$ 与 $S[j+k]$，相等则 $k \leftarrow k+1$；
- 记录 $LCP[rank[i]] = k$；
- 若 $k > 0$，则 $k \leftarrow k-1$（为下一轮提供下界）。

项目实现还提供了基于 SA+LCP 的高级查询：最长重复子串、不同子串计数、至少出现 $k$ 次的子串枚举。

**代码实现**：[`suffix_array.rs`](../../../examples/algorithms/src/suffix_array.rs)

### 3. 复杂度分析

| 步骤 | 时间复杂度 | 空间复杂度 |
|------|-----------|-----------|
| 倍增法构建 SA | $O(n \log n)$ | $O(n)$ |
| Kasai LCP | $O(n)$ | $O(n)$ |
| **总计** | **$O(n \log n)$** | **$O(n)$** |

使用 SA-IS 等线性算法可进一步将构建时间降至 $O(n)$，但实现复杂度较高。

### 4. 形式化验证 / 正确性论证

**引理 1（倍增排序的正确性）**：若所有后缀已按长度为 $k$ 的前缀有序，则以 $(rank[i], rank[i+k])$ 为关键字排序后，后缀按长度为 $2k$ 的前缀有序。

*证明*：两个后缀 $S[i..]$ 与 $S[j..]$ 的前 $2k$ 个字符相等，当且仅当前 $k$ 个字符相等（即 $rank[i]=rank[j]$）且后 $k$ 个字符相等（即 $rank[i+k]=rank[j+k]$）。因此二元组比较恰好刻画了 $2k$-前缀的字典序。$\square$

**引理 2（Kasai 下界）**：设 $i$ 的后一位置为 $i+1$，对应排名为 $rank[i+1]$，则
$LCP[rank[i+1]] \ge LCP[rank[i]] - 1$。

*证明*：设 $j = SA[rank[i]-1]$，则 $S[i..]$ 与 $S[j..]$ 有公共前缀长度为 $LCP[rank[i]]$。去掉首字符后，$S[i+1..]$ 与 $S[j+1..]$ 的公共前缀长度为 $LCP[rank[i]]-1$。而在 SA 中，$S[j+1..]$ 位于 $S[i+1..]$ 的前一个或更前的位置，因此 $S[i+1..]$ 与 SA 中其直接前驱的 LCP 至少不会更短。$\square$

**定理**：倍增法输出的 SA 正确；Kasai 算法输出的 LCP 数组正确，且时间复杂度为 $O(n)$。

*证明*：由引理 1，每次迭代排序长度翻倍，至多 $\lceil\log_2 n\rceil$ 轮后所有后缀的 $2k$-前缀互不相同的概率为 1，从而 SA 正确。引理 2 保证 Kasai 中的 $k$ 在遍历过程中总减量不超过 $n$，总增量也不超过 $n$，故比较次数 $O(n)$。$\square$

### 5. 应用场景

- **基因组学**：查找 DNA 序列中的最长重复模式、重复次数统计。
- **压缩索引**：FM-index 与后缀数组结合，支持 $O(m \log n)$ 的模式计数与定位，广泛用于生物信息学数据库（如 BWT）。
- **最长公共子串**：对两个字符串拼接后构建 SA，利用 LCP 数组跨越分隔符的最大值求解。
- **不同子串计数**：公式 $\displaystyle\frac{n(n+1)}{2} - \sum_{i=0}^{n-1} LCP[i]$ 可在 $O(n)$ 时间内得到所有不同子串数量。

### 6. 扩展变体

| 变体 | 特点 | 复杂度 |
|------|------|--------|
| **SA-IS 算法** | 基于诱导排序（Induced Sorting）的线性构建算法 | $O(n)$ 时间，$O(n)$ 空间 |
| **后缀树** | 显式存储所有后缀的压缩 Trie，支持更丰富的子串查询 | $O(n)$ 构建，但常数与空间开销更大 |
| **后缀自动机** | 识别所有子串的最小 DFA，支持在线构建 | $O(n)$ 时间，$O(n)$ 空间 |
| **LCP-RMQ** | 结合 RMQ（稀疏表/Segment Tree）在 $O(1)$ 回答任意两后缀的 LCP | 预处理 $O(n \log n)$，查询 $O(1)$ |

### 参考文献

1. **U. Manber, G. Myers**, "Suffix Arrays: A New Method for On-Line String Searches", *SIAM Journal on Computing*, 22(5), 1993.
2. **T. Kasai et al.**, "Linear-Time Longest-Common-Prefix Computation in Suffix Arrays and Its Applications", *CPM*, 2001.
3. **G. Nong, S. Zhang, W. H. Chan**, "Two Efficient Algorithms for Linear Time Suffix Array Construction", *IEEE Transactions on Computers*, 60(10), 2011.
4. **T. H. Cormen et al.**, *Introduction to Algorithms*, 3rd ed., MIT Press, 2009.
---

## 知识导航

- [返回目录](README.md)

