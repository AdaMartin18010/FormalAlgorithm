---
title: 19 van Emde Boas树
concepts: ["排序", "搜索", "图算法", "动态规划", "贪心"]
level: 中级
last_updated: 2026-04-21
---

# van Emde Boas 树（vEB Tree）


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

> 对标：CLRS 第4版 Chapter 20

## 一、理论基础

van Emde Boas 树（简称 **vEB 树**）是一种支持**动态优先队列**操作的数据结构，由 Peter van Emde Boas 于 1975 年提出。

### 核心特性

当关键字来自**有限整数 Universe** $U = \{0, 1, \dots, u-1\}$ 时，vEB 树可在 **$O(\log \log u)$** 时间内完成以下操作：

- `insert` / `delete`
- `minimum` / `maximum`
- `successor` / `predecessor`
- `member`

这是**指数级**优于平衡二叉搜索树的 $O(\log n)$ 的性能。

### 适用条件

- 关键字为**非负整数**；
- Universe 大小 $u$ 已知（通常为 $2^k$）；
- 实际存储元素数 $n$ 可以远小于 $u$。

---

## 二、算法设计

vEB 树是一种**递归分治**结构。设 Universe 大小为 $u$，将 $u$ 分为 $\sqrt{u}$ 个**簇（cluster）**，每个簇大小为 $\sqrt{u}$。

### 数据结构

一个 vEB 节点包含：

- `min`：当前集合中的最小元素（不递归存储在簇中）；
- `max`：当前集合中的最大元素（不递归存储在簇中）；
- `summary`：一棵大小为 $\sqrt{u}$ 的 vEB 树，记录哪些簇非空；
- `cluster[0..√u−1]`：每棵都是大小为 $\sqrt{u}$ 的 vEB 子树。

### 操作设计

#### 1. 插入（insert）

```text
如果树为空：
    min = max = x
否则：
    如果 x < min：交换 x 和 min
    如果 x 不在对应 cluster 中：
        在 summary 中标记该 cluster 非空
    将 x 插入对应 cluster
    如果 x > max：max = x
```

时间复杂度：$O(\log \log u)$

#### 2. 删除（delete）

删除时需要处理 `min` 和 `max` 的特殊存储方式。若删除的是 `min`，需要从 `min` 所在 cluster 中找新的最小值来替代；若该 cluster 变空，还需更新 `summary`。

时间复杂度：$O(\log \log u)$

#### 3. 后继（successor）

```text
如果 x < min：返回 min
否则：
    在 x 所在 cluster 内查找后继
    若 cluster 内无后继：
        找到下一个非空簇编号 succ_cluster
        返回 cluster[succ_cluster].min
```

时间复杂度：$O(\log \log u)$

---

## 三、复杂度分析

### 时间复杂度

| 操作 | 时间复杂度 |
|------|-----------|
| `member` | $O(\log \log u)$ |
| `minimum` / `maximum` | $O(1)$ |
| `successor` / `predecessor` | $O(\log \log u)$ |
| `insert` / `delete` | $O(\log \log u)$ |

### 空间复杂度

朴素实现需要 $O(u)$ 空间。通过**散列压缩（hashing the clusters）**可以将空间降至 $O(n \log \log u)$，但会引入期望时间上的开销。

### 递归深度

每次递归 Universe 从 $u$ 降至 $\sqrt{u}$，故递归深度为：
$$
\log \log u
$$
这是 vEB 树操作效率的根本来源。

---

## 四、形式化验证

### 关键不变式

1. **min/max 独占性**：若集合非空，`min` 和 `max` 直接存储在节点中，不出现在任何 `cluster` 内。
2. **簇一致性**：元素 $x$（$x \neq \text{min}$）一定存储在 `cluster[high(x)]` 中，位置为 `low(x)`。
3. **Summary 正确性**：`summary` 中存储的集合恰好是所有非空簇的编号集合。
4. **递归基例**：当 $u = 2$ 时，vEB 树退化为只有两个比特位的简单数组。

### 正确性证明概要

所有操作均通过**结构归纳法**证明正确：

- **基例**（$u=2$）：直接枚举验证。
- **归纳步**：假设大小为 $\sqrt{u}$ 的 vEB 树操作正确，则大小为 $u$ 的 vEB 树通过在 `summary` 和对应 `cluster` 上调用子操作完成，正确性由归纳假设保证。

---

## 五、应用场景

1. **整数优先队列**：当关键字为整数且范围不大时，vEB 树提供理论上最快的优先队列操作。
2. **图算法**：在整数权重的 Dijkstra / Prim 算法中，可作为 $O(\log \log u)$ 优先队列使用。
3. **调度器与时间片轮转**：操作系统中进程优先级为固定范围整数时，可用 vEB 树实现高效调度。
4. **后继/前驱查询**：在整数坐标、IP 地址路由前缀等离散空间中快速查找最近邻。

### 与红黑树的对比

| 场景 | 推荐结构 |
|------|----------|
| 关键字为任意可比较类型 | 红黑树 / AVL 树 |
| 关键字为固定范围整数，且 $u$ 不大 | **vEB 树** |
| 内存极度受限 | 二叉堆 / 配对堆 |

---

## 六、扩展变体

- **压缩 vEB 树（Compressed vEB Tree）**：用哈希表替代数组存储 cluster，空间降至 $O(n)$ 期望，时间仍为 $O(\log \log u)$ 期望。
- **y-fast Trie**：结合 vEB 树思想的二进制 Trie 变体，支持 $O(\log \log u)$ 操作且空间为 $O(n)$。
- **x-fast Trie**： predecessor/successor 查询 $O(\log \log u)$，空间 $O(u / \log u)$。

---

## 参考

- Cormen, T. H., et al. *Introduction to Algorithms* (4th ed.). MIT Press. Chapter 20.
- van Emde Boas, P. (1975). Preserving order in a forest in less than logarithmic time. *FOCS*.

---

## 参考文献

- 待补充

---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解van Emde Boas 树（vEB Tree）的核心概念
- 掌握van Emde Boas 树（vEB Tree）的形式化表示
