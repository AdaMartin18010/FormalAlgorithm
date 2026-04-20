---
title: 01 Johnson算法
concepts: ["排序", "搜索", "图算法", "动态规划", "贪心"]
level: 中级
last_updated: 2026-04-21
---

# Johnson 算法


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

> 对标：CLRS 第4版 Chapter 25.3

## 一、理论基础

Johnson 算法用于求解**带负权边但无负权环**的有向图的**全源最短路径（All-Pairs Shortest Paths, APSP）**问题。

### 为什么需要 Johnson 算法？

| 算法 | 适用条件 | 时间复杂度 | 局限性 |
|------|----------|-----------|--------|
| **Floyd-Warshall** | 允许负权边 | $O(V^3)$ | 稠密图快，稀疏图慢 |
| **Dijkstra × V 次** | 非负权边 | $O(V E \log V)$ | 无法处理负权边 |
| **Johnson** | 允许负权边、稀疏图 | $O(V^2 \log V + V E)$ | 不能含负权环 |

Johnson 算法的核心思想是：

1. **重赋权（Reweighting）**：通过 Bellman-Ford 计算一个势函数 $h(v)$，使得新权重 $w'(u,v) = w(u,v) + h(u) - h(v) \geq 0$；
2. **运行 Dijkstra**：在非负权图上对每个源点运行 Dijkstra；
3. **还原距离**：$d(u,v) = d'(u,v) - h(u) + h(v)$。

### 重赋权的正确性

对于任意路径 $p = v_0 \to v_1 \to \dots \to v_k$，有：
$$
w'(p) = \sum_{i=1}^{k} [w(v_{i-1}, v_i) + h(v_{i-1}) - h(v_i)] = w(p) + h(v_0) - h(v_k)
$$

因此，所有 $u \to v$ 的路径中，$w'(p)$ 最小者对应的 $w(p)$ 也最小，重赋权不改变最短路径的结构。

---

## 二、算法设计

### 步骤

1. **添加虚拟源点 $s$**：向原图中添加一个虚拟源点 $s$，并向所有顶点连一条权重为 0 的边。
2. **运行 Bellman-Ford**：以 $s$ 为源点运行 Bellman-Ford，得到 $h(v) = \delta(s, v)$。
   - 若检测到负权环，返回错误。
3. **重新赋权**：对所有边计算 $w'(u,v) = w(u,v) + h(u) - h(v)$。
4. **全源 Dijkstra**：对每个顶点 $u \in V$，在重赋权后的图上运行 Dijkstra，得到 $d'(u, v)$。
5. **距离还原**：$d(u,v) = d'(u,v) - h(u) + h(v)$。

### 关键数据结构

- **势函数数组 `h`**：长度为 $V$；
- **重赋权邻接表**：每个节点维护 `(邻居, w')` 列表；
- **距离矩阵**：$V \times V$ 的 `Option<i64>` 矩阵；
- **前驱矩阵**：用于路径重建。

---

## 三、复杂度分析

| 步骤 | 时间复杂度 | 说明 |
|------|-----------|------|
| Bellman-Ford | $O(V E)$ | 含虚拟源点 |
| 重赋权 | $O(E)$ | 遍历所有边 |
| V 次 Dijkstra | $O(V E \log V)$ | 使用二叉堆 |
| **总计** | **$O(V^2 \log V + V E)$** | 稀疏图优于 Floyd-Warshall |
| 空间复杂度 | $O(V^2 + E)$ | 距离矩阵 + 邻接表 |

---

## 四、形式化验证

### 引理 25.1（三角不等式）

Bellman-Ford 求得的势函数 $h$ 满足：对所有边 $(u,v)$，
$$
h(v) \leq h(u) + w(u,v)
$$
从而 $w'(u,v) = w(u,v) + h(u) - h(v) \geq 0$。

### 定理 25.2（路径等价性）

对任意 $u, v \in V$ 和任意路径 $p: u \leadsto v$，
$$
w'(p) = w(p) + h(u) - h(v)
$$
因此，$p$ 在 $w$ 下最短当且仅当在 $w'$ 下最短。

### 推论

Johnson 算法返回的距离矩阵 `distances[u][v]` 等于原图中 $u$ 到 $v$ 的真实最短路径长度。

---

## 五、应用场景

1. **稀疏图的全源最短路径**：公路网、社交网络等 $E \ll V^2$ 的场景，Johnson 比 Floyd-Warshall 更快。
2. **含负权边的图**：货币兑换网络（汇率套利模型）、差分约束系统等。
3. **路径规划中间件**：作为图数据库的 APSP 查询引擎组件。

### 与 Floyd-Warshall 的选型

- $E = O(V^2)$（稠密图）：两者性能接近，Floyd-Warshall 实现更简单。
- $E = O(V)$（稀疏图）：Johnson 的 $O(V^2 \log V)$ 明显优于 Floyd-Warshall 的 $O(V^3)$。

---

## 六、扩展变体

- **稀疏图优化**：使用斐波那契堆可将 V 次 Dijkstra 优化至 $O(V^2 \log V + V E)$ 中的对数项进一步降低为 $O(V E + V^2 \log V)$，在理论上有意义，工程中二叉堆通常足够。
- **动态 Johnson**：当边权增量更新时，可仅局部重计算势函数和受影响源点的 Dijkstra，避免全量重算。
- **APSP 与传递闭包**：Johnson 可扩展用于计算可达性矩阵（将存在路径设为 1，否则为 0）。

---

## 参考

- Cormen, T. H., et al. *Introduction to Algorithms* (4th ed.). MIT Press. Chapter 25.3.

---

## 参考文献

- 待补充

---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解Johnson 算法的核心概念
- 掌握Johnson 算法的形式化表示

---

---
title: 9.9.2 Johnson 算法 / Johnson's Algorithm
version: 1.0
status: maintained
last_updated: 2026-04-15
owner: 算法理论工作组
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)
> **项目导航与对标**：[项目扩展与持续推进任务编排](../../项目扩展与持续推进任务编排.md)、[国际课程对标表](../../国际课程对标表.md)

## 9.9.2 Johnson 算法 / Johnson's Algorithm (All-Pairs Shortest Paths)

### 摘要 / Executive Summary

Johnson 算法是一种求解**全对最短路径**（All-Pairs Shortest Paths, APSP）问题的算法，特别适用于**稀疏图**。它通过**重赋权**（reweighting）技术，先使用 Bellman-Ford 算法计算一组势能函数，将图中可能存在的负权边转化为非负权边，然后对每个顶点运行 Dijkstra 算法。该算法在稀疏图上的时间复杂度为 $O(V E \log V)$，优于 Floyd-Warshall 的 $O(V^3)$。本文档系统阐述 Johnson 算法的理论基础、算法设计、复杂度分析、形式化正确性验证、应用场景及扩展变体。文档对齐 CLRS 第 25.3 节 [CLRS2022] 与项目 Rust 实现 `examples/algorithms/src/johnson.rs`。

### 国际课程参考 / International Course References

- **MIT 6.006**: Introduction to Algorithms — Shortest Paths, Johnson's Algorithm
- **Stanford CS161**: Design and Analysis of Algorithms — All-Pairs Shortest Paths
- **CMU 15-451**: Algorithm Design and Analysis — Graph Algorithms

---

## 目录 / Table of Contents

- [9.9.2 Johnson 算法 / Johnson's Algorithm (All-Pairs Shortest Paths)](#992-johnson-算法--johnsons-algorithm-all-pairs-shortest-paths)
  - [摘要 / Executive Summary](#摘要--executive-summary)
  - [国际课程参考 / International Course References](#国际课程参考--international-course-references)
- [目录 / Table of Contents](#目录--table-of-contents)
- [1. 理论基础](#1-理论基础)
  - [1.1 问题定义](#11-问题定义)
  - [1.2 三角不等式与势能函数](#12-三角不等式与势能函数)
- [2. 算法设计](#2-算法设计)
  - [2.1 添加超级源点与 Bellman-Ford](#21-添加超级源点与-bellman-ford)
  - [2.2 重赋权](#22-重赋权)
  - [2.3 逐点运行 Dijkstra](#23-逐点运行-dijkstra)
  - [2.4 距离还原](#24-距离还原)
  - [2.5 Rust 实现映射](#25-rust-实现映射)
- [3. 复杂度分析](#3-复杂度分析)
- [4. 形式化验证](#4-形式化验证)
  - [4.1 不变式](#41-不变式)
  - [4.2 正确性论证](#42-正确性论证)
- [5. 应用场景](#5-应用场景)
- [6. 扩展变体](#6-扩展变体)
  - [6.1 处理大规模稀疏图](#61-处理大规模稀疏图)
  - [6.2 动态 Johnson](#62-动态-johnson)
- [参考文献 / References](#参考文献--references)

---

## 1. 理论基础

### 1.1 问题定义

**定义 1.1.1** (全对最短路径问题)

给定带权有向图 $G = (V, E)$，边权函数 $w: E \rightarrow \mathbb{R}$。全对最短路径问题要求计算所有有序顶点对 $(u, v) \in V \times V$ 之间的最短路径权重 $\delta(u, v)$。

**定义 1.1.2** (最短路径权重)

$$
\delta(u, v) = \begin{cases}
\min\{w(p) : u \xrightarrow{p} v\} & \text{if there exists a path from } u \text{ to } v \\
\infty & \text{otherwise}
\end{cases}
$$

### 1.2 三角不等式与势能函数

**定义 1.2.1** (势能函数)

函数 $h: V \rightarrow \mathbb{R}$ 称为图 $G$ 上的一个**势能函数**（potential function）。

**定义 1.2.2** (重赋权)

对每条边 $(u, v) \in E$，定义新的边权：
$$\hat{w}(u, v) = w(u, v) + h(u) - h(v)$$

**引理 1.2.3** (路径权重变化不变性)

对任意路径 $p = \langle v_0, v_1, \ldots, v_k \rangle$，有：
$$\hat{w}(p) = w(p) + h(v_0) - h(v_k)$$

*证明*：
$$
\begin{aligned}
\hat{w}(p) &= \sum_{i=1}^{k} \hat{w}(v_{i-1}, v_i) \\
&= \sum_{i=1}^{k} \left(w(v_{i-1}, v_i) + h(v_{i-1}) - h(v_i)\right) \\
&= w(p) + h(v_0) - h(v_k)
\end{aligned}
$$
∎

**推论 1.2.4**

对任意顶点对 $(u, v)$，路径 $p$ 是在 $w$ 下的最短路径当且仅当 $p$ 是在 $\hat{w}$ 下的最短路径。

*证明*：由引理 1.2.3，$\hat{w}(p) - \hat{w}(q) = w(p) - w(q)$，因此相对顺序不变。∎

---

## 2. 算法设计

### 2.1 添加超级源点与 Bellman-Ford

构造新图 $G' = (V \cup \{s\}, E \cup \{(s, v, 0) : v \in V\})$，其中 $s$ 为新增的**超级源点**（super source）。

运行 Bellman-Ford 算法从 $s$ 出发，计算最短距离 $h(v) = \delta(s, v)$。

- 若 $G'$ 中存在负权环，则原图 $G$ 亦存在负权环，算法终止并报告错误。
- 否则，由三角不等式，对任意边 $(u, v) \in E$：
  $$h(v) \leq h(u) + w(u, v) \implies \hat{w}(u, v) = w(u, v) + h(u) - h(v) \geq 0$$

### 2.2 重赋权

对原图 $G$ 的每条边重新赋权：
$$\hat{w}(u, v) \leftarrow w(u, v) + h(u) - h(v)$$

此时所有边权非负，满足 Dijkstra 算法的运行条件。

### 2.3 逐点运行 Dijkstra

对每个顶点 $u \in V$，以 $u$ 为源点在重赋权后的图 $(V, E, \hat{w})$ 上运行 Dijkstra 算法，得到 $\hat{\delta}(u, v)$ 及前驱信息。

### 2.4 距离还原

利用引理 1.2.3 将重赋权后的距离还原为真实最短路径距离：
$$\delta(u, v) = \hat{\delta}(u, v) - h(u) + h(v)$$

### 2.5 Rust 实现映射

项目实现位于 `examples/algorithms/src/johnson.rs`：

| 理论步骤 | Rust 实现对应 |
|:---|:---|
| 超级源点 + Bellman-Ford | 调用 `bellman_ford(&bf_edges, s)` |
| 势能函数 $h$ | `h: Vec<W>` |
| 重赋权 | `hw = w + h[u] - h[v]` |
| 逐点 Dijkstra | 私有函数 `dijkstra_indexed(n, &reweighted, u)` |
| 距离还原 | `dv - h[u] + h[v]` |
| 路径重建 | `JohnsonResult::path(u, v)` |

---

## 3. 复杂度分析

**定理 3.1** (Johnson 算法时间复杂度)

设图 $G = (V, E)$，使用二叉堆实现的 Dijkstra 算法，则 Johnson 算法的时间复杂度为：
$$T(V, E) = O(V E \log V)$$

*证明*：

- Bellman-Ford（含超级源点）：$O(V \cdot (E + V)) = O(V E + V^2)$
- 对每个顶点运行 Dijkstra：$V \cdot O((E + V) \log V) = O(V E \log V + V^2 \log V)$
- 对于稀疏图（$E = o(V^2)$），主导项为 $O(V E \log V)$。∎

**定理 3.2** (空间复杂度)

$$S(V, E) = O(V^2)$$

*证明*：需要存储 $V \times V$ 的距离矩阵与后继矩阵。∎

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 |
|:---|:---|:---|:---|
| Floyd-Warshall | $O(V^3)$ | $O(V^2)$ | 稠密图、负权边 |
| Johnson | $O(V E \log V)$ | $O(V^2)$ | 稀疏图、负权边（无负权环） |
| 重复 Dijkstra (无负权) | $O(V E \log V)$ | $O(V^2)$ | 稀疏图、全非负权边 |

---

## 4. 形式化验证

### 4.1 不变式

**I-1. 非负重赋权**：在执行 Dijkstra 前，所有重赋权后的边权满足 $\hat{w}(u, v) \geq 0$。

**I-2. 最短路径等价性**：对任意顶点对 $(u, v)$，路径 $p$ 是 $w$ 下的最短路径当且仅当 $p$ 是 $\hat{w}$ 下的最短路径。

**I-3. 距离还原正确性**：最终输出的距离矩阵满足 $dist[u][v] = \delta(u, v)$。

### 4.2 正确性论证

**定理 4.2.1** (重赋权非负性)

若原图 $G$ 中不存在从超级源点可达的负权环，则对所有边 $(u, v) \in E$，有 $\hat{w}(u, v) \geq 0$。

*证明*：$h(v) = \delta(s, v)$ 满足三角不等式：
$$h(v) \leq h(u) + w(u, v)$$
移项即得 $\hat{w}(u, v) = w(u, v) + h(u) - h(v) \geq 0$。∎

**定理 4.2.2** (Dijkstra 结果正确性)

在重赋权后的图 $(V, E, \hat{w})$ 上运行 Dijkstra，得到的 $\hat{\delta}(u, v)$ 即为该图中 $u$ 到 $v$ 的真实最短距离。

*证明*：由定理 4.2.1，所有边权非负，满足 Dijkstra 算法的适用条件，故 Dijkstra 正确。∎

**定理 4.2.3** (Johnson 算法正确性)

对任意顶点对 $(u, v)$，Johnson 算法输出 $\delta(u, v) = \hat{\delta}(u, v) - h(u) + h(v)$ 为原图中最短路径权重。

*证明*：

- 由推论 1.2.4，重赋权不改变最短路径的拓扑结构。
- 设 $p$ 为 $u$ 到 $v$ 的最短路径，则 $\hat{\delta}(u, v) = \hat{w}(p) = w(p) + h(u) - h(v) = \delta(u, v) + h(u) - h(v)$。
- 移项即得 $\delta(u, v) = \hat{\delta}(u, v) - h(u) + h(v)$。∎

**定理 4.2.4** (负权环检测)

若原图 $G$ 中存在负权环，则 Johnson 算法在 Bellman-Ford 阶段即可检测并报告。

*证明*：超级源点 $s$ 向所有顶点连零权边，故 $G$ 中任意可达的负权环在 $G'$ 中亦从 $s$ 可达。Bellman-Ford 可检测从 $s$ 可达的负权环。∎

---

## 5. 应用场景

| 应用场景 | 说明 |
|:---|:---|
| **稀疏图 APSP** | 当 $E \ll V^2$ 时，Johnson 的 $O(V E \log V)$ 显著优于 Floyd-Warshall。 |
| **含负权边的路网** | 交通网络中某些路段可能因补贴/拥堵收费出现负权，Johnson 可在保证效率的同时处理负权。 |
| **网络直径计算** | 全对最短路径结果是计算图直径、偏心率等中心性指标的基础。 |
| **差分约束系统** | Bellman-Ford 求解的势函数与差分约束的对偶问题密切相关。 |
| **动态图查询** | 作为静态预处理步骤，为后续大量最短路径查询提供距离矩阵。 |

---

## 6. 扩展变体

### 6.1 处理大规模稀疏图

对于顶点数极大但边数极少的图，可以使用**斐波那契堆**（Fibonacci Heap）将 Dijkstra 的单源复杂度降至 $O(E + V \log V)$，从而将 Johnson 的整体复杂度优化至 $O(V E + V^2 \log V)$。

### 6.2 动态 Johnson

在图发生少量边权更新时，无需重新运行完整的 Johnson 算法。可以：

- 仅更新受影响的势能函数；
- 或使用**动态全对最短路径**（Dynamic APSP）算法进行增量维护，如 Demetrescu 与 Italiano 的动态矩阵方法。

---

## 参考文献 / References

1. **[CLRS2022]** Cormen, T. H., Leiserson, C. E., Rivest, R. L., & Stein, C. (2022). *Introduction to Algorithms* (4th ed.). MIT Press. — 第 25.3 节：用于稀疏图的 Johnson 算法。
2. **[Johnson1977]** Johnson, D. B. (1977). "Efficient Algorithms for Shortest Paths in Sparse Networks". *Journal of the ACM*, 24(1), 1-13.
3. **[Tarjan1983]** Tarjan, R. E. (1983). *Data Structures and Network Algorithms*. SIAM. — 关于势能函数与重赋权的系统论述。

**文档版本 / Document Version**: 1.0
**最后更新 / Last Updated**: 2026-04-15
**状态 / Status**: maintained
**Rust 实现引用**: `examples/algorithms/src/johnson.rs`
---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解02-Johnson算法的核心概念
- 掌握02-Johnson算法的形式化表示
