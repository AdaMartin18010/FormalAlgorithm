---
title: 02 Hopcroft Karp算法
concepts: ["排序", "搜索", "图算法", "动态规划", "贪心"]
level: 中级
last_updated: 2026-04-21
---

# Hopcroft-Karp 算法


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

> 对标：CLRS 第4版 Chapter 26.6

## 一、理论基础

Hopcroft-Karp 算法由 John Hopcroft 与 Richard Karp 于 1973 年提出，用于在**无权二分图**中求解**最大匹配（Maximum Bipartite Matching）**。

### 核心突破

传统的匈牙利算法（DFS 增广）最坏时间复杂度为 $O(V E)$。Hopcroft-Karp 通过**批量寻找最短增广路径**，将复杂度优化至：

$$
O(E \cdot \sqrt{V})
$$

这是二分图最大匹配问题的**经典最优算法**之一。

### 关键洞察

在二分图中，设当前匹配大小为 $M$。若存在**长度为 $k$ 的增广路径**，则每找到并增广一条该路径，匹配大小增加 1。Hopcroft-Karp 的证明表明：

- 每次 BFS 分层后，所有找到的最短增广路径长度相同；
- 每完成一轮 BFS + DFS 批量增广，最短增广路径长度严格增加；
- 因此最多需要 $O(\sqrt{V})$ 轮即可找到全部最大匹配。

---

## 二、算法设计

### 数据结构

- `match_left[u]`：左侧顶点 $u$ 匹配的右侧顶点（`None` 表示未匹配）；
- `match_right[v]`：右侧顶点 $v$ 匹配的左侧顶点；
- `dist[u]`：左侧顶点 $u$ 到最近未匹配右侧顶点的 BFS 距离（分层用）。

### 算法流程

```text
初始化 match_left 和 match_right 为 None
while BFS 能找到增广路径:
    for 每个左侧未匹配点 u:
        if DFS(u) 成功增广:
            matching_size += 1
return 匹配结果
```

#### 1. BFS 分层

- 将所有左侧未匹配点加入队列，距离设为 0；
- 左侧已匹配点距离设为 INF；
- 沿边遍历：
  - 若右侧顶点 $v$ 已匹配到左侧 $u'$，且 $u'$ 未被访问，则将 $u'$ 入队，距离为当前距离 + 1；
  - 若右侧顶点 $v$ 未匹配，说明找到了一条最短增广路径的终点，记录 `found = true`。

#### 2. DFS 批量增广

- 从左侧未匹配点 $u$ 出发，只允许沿 BFS 分层图中 `dist` 严格递增的边前进；
- 若到达未匹配的右侧顶点，则执行增广（更新 `match_left` 和 `match_right`），返回 `true`；
- 若从 $u$ 出发的所有尝试均失败，将 `dist[u]` 设为 INF（剪枝，避免重复搜索）。

---

## 三、复杂度分析

| 步骤 | 时间复杂度 | 说明 |
|------|-----------|------|
| BFS | $O(E)$ | 每轮遍历所有边一次 |
| DFS 批量增广 | $O(E)$ | 每轮每条边最多被访问常数次 |
| 总轮数 | $O(\sqrt{V})$ | 最短增广路径长度最多增长 $O(\sqrt{V})$ 次 |
| **总计** | **$O(E \cdot \sqrt{V})$** | 经典二分图匹配上界 |
| 空间复杂度 | $O(V + E)$ | 邻接表 + 匹配数组 + BFS 队列 |

---

## 四、形式化验证

### 关键引理

**引理 26.7（最短增广路径长度递增）**：
设第 $i$ 轮 BFS 找到的最短增广路径长度为 $k_i$。在完成该轮所有 DFS 增广后，下一轮的最短增广路径长度 $k_{i+1} > k_i$。

**引理 26.8（轮数上界）**：
若当前匹配与最大匹配相差 $d$ 条边，则最短增广路径长度不超过 $2 \lfloor \sqrt{d} \rfloor + 1$。因此最多 $O(\sqrt{V})$ 轮后算法终止。

### 正确性证明概要

1. **BFS 分层正确性**：`dist[u]` 准确反映了从 $u$ 到某个未匹配右侧顶点的最短增广路径长度；
2. **DFS 沿分层图增广**：保证每次增广的都是当前最短长度的增广路径，不破坏已找到的最短路径结构；
3. **匹配递增**：每条增广路径使匹配大小增加 1；
4. **终止条件**：当 BFS 无法找到增广路径时，根据 Berge 定理，当前匹配即为最大匹配。

---

## 五、应用场景

1. **任务分配**：将 $n$ 个工人分配给 $m$ 个任务，每个工人只能做部分任务，求最大匹配数。
2. **网络流建模**：二分图最大匹配可转化为最大流问题（源点→左侧容量1，左侧→右侧容量1，右侧→汇点容量1）。Hopcroft-Karp 是该特殊流问题的专用优化算法。
3. **计算机视觉**：图像特征点匹配、立体视觉中的对应点搜索。
4. **推荐系统**：用户-物品二分图中的最大关联推荐。

### 与匈牙利算法的对比

| 算法 | 时间复杂度 | 适用场景 |
|------|-----------|----------|
| 匈牙利算法（DFS） | $O(V E)$ | 中小规模、实现简单 |
| **Hopcroft-Karp** | **$O(E \sqrt{V})$** | **大规模二分图、竞赛/工程首选** |
| 最大流（Dinic） | $O(E \sqrt{V})$ | 通用网络流，带权或容量不均时更灵活 |

---

## 六、扩展变体

- **带权二分图匹配（Assignment Problem）**：使用匈牙利算法（Kuhn-Munkres）在 $O(V^3)$ 内求解最大权匹配。
- **一般图最大匹配**：Edmonds 的 Blossom 算法，复杂度 $O(V^3)$ 或 $O(V E \log V)$。
- **Online 二分图匹配**：顶点按流到达，只能使用贪心或随机化策略，竞争比为 $1 - 1/e$（Karp-Vazirani-Vazirani 定理）。
- **b-匹配**：每个顶点可以与多个顶点匹配，可用网络流或线性规划求解。

---

## 参考

- Cormen, T. H., et al. *Introduction to Algorithms* (4th ed.). MIT Press. Chapter 26.6.
- Hopcroft, J. E., & Karp, R. M. (1973). An $n^{5/2}$ algorithm for maximum matchings in bipartite graphs. *SIAM J. Comput.*, 2(4), 225–231.

---

## 参考文献

- 待补充

---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解Hopcroft-Karp 算法的核心概念
- 掌握Hopcroft-Karp 算法的形式化表示

---

---
title: 9.9.3 Hopcroft-Karp 算法 / Hopcroft-Karp Algorithm
version: 1.0
status: maintained
last_updated: 2026-04-15
owner: 算法理论工作组
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)
> **项目导航与对标**：[项目扩展与持续推进任务编排](../../项目扩展与持续推进任务编排.md)、[国际课程对标表](../../国际课程对标表.md)

## 9.9.3 Hopcroft-Karp 算法 / Hopcroft-Karp Algorithm (Maximum Bipartite Matching)

### 摘要 / Executive Summary

Hopcroft-Karp 算法是求解**二分图最大匹配**（Maximum Bipartite Matching）问题的经典算法，由 John Hopcroft 与 Richard Karp 于 1973 年提出。该算法的核心思想是：在每一阶段，通过 BFS 寻找所有**最短增广路**的长度，然后通过 DFS 找出尽可能多的**点不交最短增广路**并同时进行增广。该策略将算法的时间复杂度从朴素匈牙利算法的 $O(V \cdot E)$ 降低至 $O(E \sqrt{V})$。本文档系统阐述 Hopcroft-Karp 算法的理论基础、算法设计、复杂度分析、形式化正确性验证、应用场景及扩展变体。文档对齐 CLRS 第 26 章问题 26-6 [CLRS2022] 与项目 Rust 实现 `examples/algorithms/src/hopcroft_karp.rs`。

### 国际课程参考 / International Course References

- **MIT 6.006**: Introduction to Algorithms — Graph Search, Matching
- **Stanford CS161**: Design and Analysis of Algorithms — Bipartite Matching
- **CMU 15-451**: Algorithm Design and Analysis — Network Flow, Matching

---

## 目录 / Table of Contents

- [9.9.3 Hopcroft-Karp 算法 / Hopcroft-Karp Algorithm (Maximum Bipartite Matching)](#993-hopcroft-karp-算法--hopcroft-karp-algorithm-maximum-bipartite-matching)
  - [摘要 / Executive Summary](#摘要--executive-summary)
  - [国际课程参考 / International Course References](#国际课程参考--international-course-references)
- [目录 / Table of Contents](#目录--table-of-contents)
- [1. 理论基础](#1-理论基础)
  - [1.1 二分图与匹配](#11-二分图与匹配)
  - [1.2 增广路](#12-增广路)
  - [1.3 最短增广路与点不交性](#13-最短增广路与点不交性)
- [2. 算法设计](#2-算法设计)
  - [2.1 算法框架](#21-算法框架)
  - [2.2 BFS 分层](#22-bfs-分层)
  - [2.3 DFS 多点增广](#23-dfs-多点增广)
  - [2.4 Rust 实现映射](#24-rust-实现映射)
- [3. 复杂度分析](#3-复杂度分析)
- [4. 形式化验证](#4-形式化验证)
  - [4.1 不变式](#41-不变式)
  - [4.2 正确性论证](#42-正确性论证)
- [5. 应用场景](#5-应用场景)
- [6. 扩展变体](#6-扩展变体)
  - [6.1 二分图最大权匹配](#61-二分图最大权匹配)
  - [6.2 一般图最大匹配](#62-一般图最大匹配)
  - [6.3 在线匹配](#63-在线匹配)
- [参考文献 / References](#参考文献--references)

---

## 1. 理论基础

### 1.1 二分图与匹配

**定义 1.1.1** (二分图)

图 $G = (V, E)$ 称为**二分图**（bipartite graph），若顶点集 $V$ 可被划分为两个不相交的子集 $L$ 和 $R$（即 $L \cup R = V, L \cap R = \emptyset$），且每条边 $(u, v) \in E$ 都满足 $u \in L, v \in R$。

**定义 1.1.2** (匹配)

$M \subseteq E$ 称为图 $G$ 的一个**匹配**，若 $M$ 中任意两条边没有公共端点。即：
$$\forall e_1, e_2 \in M: e_1 \cap e_2 = \emptyset$$

**最大匹配**：基数 $|M|$ 最大的匹配。

### 1.2 增广路

**定义 1.2.1** (交替路与增广路)

对于二分图 $G = (L \cup R, E)$ 和匹配 $M$，一条**交替路**（alternating path）是指路径上的边交替地属于 $E \setminus M$ 和 $M$。

一条**增广路**（augmenting path）是指起点和终点均为未匹配顶点的交替路。

**引理 1.2.2** (Berge 定理)

匹配 $M$ 是最大匹配当且仅当图中不存在关于 $M$ 的增广路。

*证明概要*：

- (⇒) 若存在增广路 $P$，则 $M \oplus P$ 仍是匹配且 $|M \oplus P| = |M| + 1$，与 $M$ 最大矛盾。
- (⇐) 若 $M$ 不是最大匹配，设 $M^*$ 为最大匹配，则 $M \oplus M^*$ 中必含至少 $|M^*| - |M|$ 条点不交增广路。∎

### 1.3 最短增广路与点不交性

Hopcroft-Karp 算法的关键在于：每一轮不是只找一条增广路，而是找出一组**最短且点不交**的增广路，同时进行增广。

**定义 1.3.1** (最短增广路)

设 $M$ 为当前匹配，$l$ 为关于 $M$ 的增广路的最小边数，则称长度为 $l$ 的增广路为**最短增广路**。

**引理 1.3.2** (Hopcroft-Karp 核心引理)

设 $P = \{P_1, \ldots, P_k\}$ 为关于 $M$ 的极大点不交最短增广路集合，$M' = M \oplus (P_1 \cup \cdots \cup P_k)$。则关于 $M'$ 的最短增广路长度严格大于关于 $M$ 的最短增广路长度。

*证明概要*：参见 [CLRS2022] 问题 26-6 的 (c)-(d) 部分。若存在长度仍为 $l$ 的增广路 $Q$，则 $Q$ 必与某条 $P_i$ 共享顶点，通过分析对称差可导出 $|Q| > l$ 的矛盾。∎

---

## 2. 算法设计

### 2.1 算法框架

```
HOPCROFT-KARP(G)
    M = ∅
    repeat
        使用 BFS 计算最短增广路长度 l
        使用 DFS 找出一组极大点不交的最短增广路集合 P
        M = M ⊕ (∪_{P_i ∈ P} P_i)
    until P = ∅
    return M
```

### 2.2 BFS 分层

BFS 从所有**未匹配的左部顶点**出发，沿交替边（未匹配边 → 匹配边 → 未匹配边 → ...）进行搜索，计算每个左部顶点到最短增广路终点的距离层级。

- 若 BFS 能到达某个未匹配的右部顶点，则说明存在增广路，返回 `true`。
- 否则返回 `false`，算法终止。

### 2.3 DFS 多点增广

DFS 限制在 BFS 构建的分层图上进行：只允许从距离为 $d$ 的左部顶点走到距离为 $d+1$ 的左部顶点。对每个未匹配的左部顶点发起一次 DFS，寻找一条增广路。若成功，立即更新匹配。

DFS 失败后，将该顶点的距离标记为 $\infty$，避免后续重复搜索。

### 2.4 Rust 实现映射

项目实现位于 `examples/algorithms/src/hopcroft_karp.rs`：

| 理论步骤 | Rust 实现对应 |
|:---|:---|
| BFS 分层 | `bfs()` 构建 `dist` 数组 |
| DFS 增广 | `dfs_hopcroft_karp()` 递归寻找增广路 |
| 匹配更新 | `pair_left[u] = Some(v)`, `pair_right[v] = Some(u)` |
| 结果提取 | `HopcroftKarpResult::edges()` |

---

## 3. 复杂度分析

**定理 3.1** (Hopcroft-Karp 时间复杂度)

二分图 $G = (L \cup R, E)$ 上，Hopcroft-Karp 算法的时间复杂度为：
$$T(V, E) = O(E \sqrt{V})$$

*证明*：

- 每轮 BFS 与所有 DFS 的总工作量均为 $O(E)$。
- 设第 $i$ 轮的最短增广路长度为 $l_i$。由引理 1.3.2，$l_i$ 严格递增。
- 在前 $\sqrt{V}$ 轮中，每轮至少增广一条路径，匹配大小至少增加 1，故匹配大小至少增加 $\sqrt{V}$。
- 由 Berge 定理的推论，若当前匹配与最大匹配相差 $k$，则至少存在 $k$ 条点不交增广路。当最短增广路长度 $\geq 2\sqrt{V} + 1$ 时，这些路径覆盖的顶点数 $> V$，故 $k < \sqrt{V}$。
- 因此总轮数 $O(\sqrt{V})$，总时间 $O(E \sqrt{V})$。∎

**定理 3.2** (空间复杂度)

$$S(V, E) = O(V + E)$$

*证明*：需要存储邻接表、匹配数组及 BFS 距离数组。∎

| 算法 | 时间复杂度 | 空间复杂度 | 说明 |
|:---|:---|:---|:---|
| 匈牙利算法 (DFS) | $O(V \cdot E)$ | $O(V)$ | 实现简单 |
| 匈牙利算法 (BFS) | $O(V \cdot E)$ | $O(V)$ | 找最短增广路 |
| Hopcroft-Karp | $O(E \sqrt{V})$ | $O(V + E)$ | 大规模图最优 |

---

## 4. 形式化验证

### 4.1 不变式

**I-1. 匹配合法性**：`pair_left` 与 `pair_right` 始终互为逆映射，即若 `pair_left[u] = Some(v)`，则必有 `pair_right[v] = Some(u)`。

**I-2. 交替路约束**：BFS 仅沿交替边（未匹配边从左到右，匹配边从右到左）扩展，因此 BFS 树中的每条路径都是关于当前匹配的交替路。

**I-3. 最短增广路单调性**：设第 $i$ 轮的最短增广路长度为 $l_i$，则 $l_{i+1} > l_i$。

### 4.2 正确性论证

**定理 4.2.1** (增广操作保持匹配)

若 $P$ 是关于匹配 $M$ 的增广路，则 $M \oplus P$ 仍是匹配，且 $|M \oplus P| = |M| + 1$。

*证明*：增广路 $P$ 上的边交替属于 $E \setminus M$ 和 $M$，且两端点未匹配。将 $P$ 上的匹配边与非匹配边互换后，所有顶点仍最多关联一条匹配边，匹配大小增加 1。∎

**定理 4.2.2** (BFS 正确性)

BFS 返回 `true` 当且仅当当前匹配存在增广路。

*证明*：

- 若 BFS 到达未匹配右部顶点，则由交替路的构造，存在从某个未匹配左部顶点到该未匹配右部顶点的交替路，即增广路。
- 若不存在增广路，则所有从未匹配左部顶点出发的交替路都无法到达未匹配右部顶点，BFS 无法标记到自由右部顶点。∎

**定理 4.2.3** (DFS 增广路存在性)

若 BFS 标记了某个未匹配右部顶点为可达，则对每个未匹配左部顶点 $u$，DFS(u) 返回 `true` 当且仅当存在一条从 $u$ 出发的最短增广路。

*证明*：DFS 仅在 BFS 分层图上沿距离递增的方向搜索，因此找到的任何增广路长度都等于最短增广路长度 $l$。对 $u$ 进行归纳：若 $u$ 有直接邻居 $v$ 未匹配，则找到增广路；否则沿匹配边递归到 $u' = pair_right[v]$，由归纳假设，若 $u'$ 存在最短增广路，则 $u$ 也存在。∎

**定理 4.2.4** (Hopcroft-Karp 正确性)

算法终止时返回的匹配 $M$ 是最大匹配。

*证明*：

- 由定理 4.2.1，每次增广操作保持匹配合法性并严格增加匹配大小。
- 由定理 4.2.2，算法仅在不存在增广路时终止。
- 由 Berge 定理（引理 1.2.2），不存在增广路的匹配必为最大匹配。∎

---

## 5. 应用场景

| 应用场景 | 说明 |
|:---|:---|
| **任务分配** | 将 $n$ 个工人分配给 $m$ 个任务，每个人只能做部分任务，求最大分配数。 |
| **推荐系统** | 二部图左侧为用户，右侧为物品，匹配模型用于最大化可推荐覆盖。 |
| **计算机视觉** | 双目视觉中的特征点匹配、目标跟踪中的点对应问题。 |
| **网络流** | 二分图最大匹配可规约为最大流问题，Hopcroft-Karp 是专用的高效解法。 |
| **调度问题** | 课程与教室、航班与登机口等资源匹配问题。 |

---

## 6. 扩展变体

### 6.1 二分图最大权匹配

在最大匹配基础上引入边权，求解总权重最大的匹配。经典算法为**匈牙利算法**（Kuhn-Munkres），时间复杂度 $O(V^3)$。

### 6.2 一般图最大匹配

对于非二分图，Edmonds 提出的**开花算法**（Blossom Algorithm）可处理奇圈（开花），最优实现时间复杂度为 $O(E \sqrt{V})$（Micali-Vazirani）。

### 6.3 在线匹配

顶点按顺序到达，算法必须在顶点到达时立即做出匹配决策且不可撤销。典型模型包括：

- **随机到达模型**：Ranking 算法可达到 $(1 - 1/e)$ 竞争比。
- **对抗到达模型**：贪心算法竞争比为 $1/2$。

---

## 参考文献 / References

1. **[CLRS2022]** Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2022). *Introduction to Algorithms* (4th ed.). MIT Press. — 第 26 章问题 26-6：Hopcroft-Karp 二分匹配算法。
2. **[HopcroftKarp1973]** Hopcroft, J. E., & Karp, R. M. (1973). "An $n^{5/2}$ Algorithm for Maximum Matchings in Bipartite Graphs". *SIAM Journal on Computing*, 2(4), 225-231.
3. **[MicaliVazirani1980]** Micali, S., & Vazirani, V. V. (1980). "An $O(\sqrt{|V|} \cdot |E|)$ Algorithm for Finding Maximum Matching in General Graphs". *Proceedings of FOCS*, 17-27.

**文档版本 / Document Version**: 1.0
**最后更新 / Last Updated**: 2026-04-15
**状态 / Status**: maintained
**Rust 实现引用**: `examples/algorithms/src/hopcroft_karp.rs`
---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解03-Hopcroft-Karp算法的核心概念
- 掌握03-Hopcroft-Karp算法的形式化表示
