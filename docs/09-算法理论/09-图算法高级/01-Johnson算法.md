# Johnson 算法

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
