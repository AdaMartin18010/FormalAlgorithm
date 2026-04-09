# Dijkstra算法 (Dijkstra's Algorithm)

> **学科**: 算法设计与分析
> **难度**: ★★★★☆
> **先修**: 图论基础、优先队列、贪心算法
> **学时**: 6小时
> **来源**: CLRS第24章、算法导论
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
Dijkstra算法是一种解决**单源最短路径问题**的贪心算法，由Edsger W. Dijkstra于1956年提出。算法适用于**非负权重**的带权有向图，计算从源点到所有其他顶点的最短路径。

**问题定义**:
给定带权有向图G=(V, E)，权重函数w: E → R_{≥0}，源点s ∈ V，求s到所有v ∈ V的最短路径长度δ(s, v)。

**算法概述**:

```
初始化: d[s] = 0, 对所有v ≠ s, d[v] = ∞
维护已确定最短距离的顶点集合S
重复n次:
    选择V-S中d值最小的顶点u
    将u加入S
    对u的每个邻居v: 松弛操作relax(u, v)
```

**关键要点**:

- **贪心策略**: 每次选择当前距离估计最小的顶点
- **非负权重要求**: 负权边会导致错误结果
- **最优性保证**: 当边权非负时，算法总能找到最优解
- **时间复杂度**: O((V+E)logV)（使用二叉堆）

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 时间复杂度（数组） | O(V²) | 稠密图适用 |
| 时间复杂度（二叉堆） | O((V+E)logV) | 稀疏图适用 |
| 时间复杂度（斐波那契堆） | O(V logV + E) | 理论最优 |
| 空间复杂度 | O(V) | 存储距离和前驱 |
| 适用范围 | 非负权重图 | 负权边需用Bellman-Ford |
| 正确性 | 保证最优 | 基于贪心选择性质 |

### 1.3 变体

**使用不同优先队列实现**:

- **数组**: O(V²)，稠密图优选
- **二叉堆**: O((V+E)logV)，通用实现
- **斐波那契堆**: O(V logV + E)，稠密图理论最优
- **双向Dijkstra**: 同时从源点和目标点搜索
- **A*算法**: 使用启发式函数指导搜索

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| 图的基本概念 | ⭐⭐⭐⭐⭐ | 理解顶点、边、有向图、加权图 |
| 优先队列/堆 | ⭐⭐⭐⭐⭐ | 能实现extract-min和decrease-key |
| 贪心算法 | ⭐⭐⭐⭐⭐ | 理解贪心选择性质 |
| 最短路径概念 | ⭐⭐⭐⭐⭐ | 理解路径权重和最短路径定义 |

### 2.2 相关概念

**紧密相关**:

- **Bellman-Ford算法** - 可处理负权边，检测负环
- **SPFA算法** - Bellman-Ford的队列优化版本
- **Floyd-Warshall算法** - 全源最短路径
- **Prim算法** - 最小生成树，结构与Dijkstra相似

### 2.3 思维导图

```
Dijkstra算法
├── 核心思想
│   ├── 贪心选择
│   ├── 松弛操作
│   └── 距离估计更新
├── 数据结构
│   ├── 优先队列（堆）
│   ├── 距离数组
│   └── 前驱数组
├── 复杂度分析
│   ├── O(V²) - 数组实现
│   ├── O((V+E)logV) - 二叉堆
│   └── O(VlogV + E) - 斐波那契堆
└── 应用场景
    ├── GPS导航
    ├── 网络路由
    └── 游戏寻路
```

---

## 三、形式化证明

### 3.1 核心定理

**定理 1** (Dijkstra算法正确性): 对于非负权重的带权有向图，Dijkstra算法终止时，对所有v ∈ V，有d[v] = δ(s, v)。

**证明**（使用循环不变式）:

```
循环不变式: 当u被加入集合S时，d[u] = δ(s, u)。

初始化: S = ∅，不变式空真成立。

保持: 假设不变式在将u加入S之前成立，需证d[u] = δ(s, u)。

反证法:
假设d[u] ≠ δ(s, u)，由于d[u]是某条路径长度，d[u] ≥ δ(s, u)。
因此d[u] > δ(s, u)，存在一条从s到u的更短路径p。

设p上第一个不在S中的顶点为y，其前驱x在S中。
由于x在S中，由归纳假设d[x] = δ(s, x)。
当x加入S时，执行了relax(x, y)，因此:
d[y] ≤ δ(s, x) + w(x, y) = δ(s, y) ≤ δ(s, u) < d[u]

但u的选择是d值最小的顶点，应有d[u] ≤ d[y]，矛盾！

因此d[u] = δ(s, u)，不变式保持。
终止: 所有顶点都在S中，d[v] = δ(s, v)对所有v成立。∎
```

### 3.2 复杂度分析

| 实现方式 | Extract-Min | Decrease-Key | 总时间 |
|----------|-------------|--------------|--------|
| 数组 | O(V) | O(1) | O(V²) |
| 二叉堆 | O(logV) | O(logV) | O((V+E)logV) |
| 斐波那契堆 | O(logV) | O(1) | O(VlogV + E) |

---

## 四、算法详解

### 4.1 伪代码（使用优先队列）

```
算法: Dijkstra(G, w, s)
输入: 图G，权重函数w，源点s
输出: 距离数组d和前驱数组π

1.  Initialize-Single-Source(G, s)
2.  S = ∅
3.  Q = V[G]  // 优先队列，按d值排序
4.  while Q ≠ ∅ do
5.      u = Extract-Min(Q)
6.      S = S ∪ {u}
7.      for each vertex v ∈ Adj[u] do
8.          Relax(u, v, w)
9.      end for
10. end while

Relax(u, v, w):
1.  if d[v] > d[u] + w(u, v) then
2.      d[v] = d[u] + w(u, v)
3.      π[v] = u
4.      Decrease-Key(Q, v, d[v])
5.  end if
```

---

## 五、示例与代码

### 5.1 标准示例

**示例**: 计算从顶点A到所有其他顶点的最短路径

```
    4       1
A ------> B ------> C
|         | 2       |
| 5       v         | 3
+-------> D ------> E

          1
```

**执行过程**:

| 步骤 | 当前u | S集合 | d[A] | d[B] | d[C] | d[D] | d[E] |
|------|-------|-------|------|------|------|------|------|
| 初始化 | - | ∅ | 0 | ∞ | ∞ | ∞ | ∞ |
| 1 | A | {A} | 0 | 4 | ∞ | 5 | ∞ |
| 2 | B | {A,B} | 0 | 4 | 5 | 5 | ∞ |
| 3 | C | {A,B,C} | 0 | 4 | 5 | 5 | 8 |
| 4 | D | {A,B,C,D} | 0 | 4 | 5 | 5 | 6 |
| 5 | E | {A,B,C,D,E} | 0 | 4 | 5 | 5 | 6 |

### 5.2 Python实现

```python
import heapq
from typing import Dict, List, Tuple, Optional


def dijkstra_heap(graph: Dict[str, Dict[str, int]], start: str) -> Tuple[Dict[str, int], Dict[str, Optional[str]]]:
    """堆实现 - O((V+E)logV)，适合稀疏图"""
    dist = {v: float('inf') for v in graph}
    dist[start] = 0
    prev = {v: None for v in graph}

    pq = [(0, start)]
    visited = set()

    while pq:
        d, u = heapq.heappop(pq)

        if u in visited:
            continue
        visited.add(u)

        for v, weight in graph.get(u, {}).items():
            if dist[u] + weight < dist[v]:
                dist[v] = dist[u] + weight
                prev[v] = u
                heapq.heappush(pq, (dist[v], v))

    return dist, prev


def reconstruct_path(prev: Dict[str, Optional[str]], start: str, end: str) -> Optional[List[str]]:
    """根据前驱数组重建路径"""
    if prev[end] is None and end != start:
        return None

    path = []
    current = end
    while current is not None:
        path.append(current)
        current = prev[current]

    return path[::-1]


# 测试
if __name__ == "__main__":
    graph = {
        'A': {'B': 4, 'D': 5},
        'B': {'C': 1, 'D': 2},
        'C': {'E': 3},
        'D': {'E': 1},
        'E': {}
    }

    dist, prev = dijkstra_heap(graph, 'A')

    print("从A出发的最短距离:")
    for v in sorted(graph.keys()):
        path = reconstruct_path(prev, 'A', v)
        print(f"  到{v}: {dist[v]}, 路径: {' -> '.join(path)}")
```

---

## 六、习题

### 6.1 理解题

1. **为什么Dijkstra不适用于负权图？** [难度⭐]

   <details>
   <summary>解答</summary>
   Dijkstra的贪心选择基于"一旦顶点被加入S，其最短距离已确定"的假设。这个假设依赖非负权重：如果所有边权非负，任何经过未访问顶点的路径长度至少为当前d值。但存在负权边时，后续可能找到更短路径，导致贪心选择错误。
   </details>

### 6.2 应用题

1. **计数最短路径** [难度⭐⭐]

   修改Dijkstra算法，计算从源点到每个顶点的最短路径数量。

   <details>
   <summary>解答</summary>

   ```python

def dijkstra_count_paths(graph, start):
    dist = {v: float('inf') for v in graph}
    count = {v: 0 for v in graph}
    dist[start] = 0
    count[start] = 1

    pq = [(0, start)]

    while pq:
        d, u = heapq.heappop(pq)
        if d > dist[u]:
            continue

        for v, w in graph[u].items():
            new_dist = dist[u] + w
            if new_dist < dist[v]:
                dist[v] = new_dist
                count[v] = count[u]
                heapq.heappush(pq, (new_dist, v))
            elif new_dist == dist[v]:
                count[v] += count[u]

    return dist, count

   ```

   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用原因 |
|----------|----------|----------|
| GPS导航 | 路径规划 | 道路网络非负权重，需要最优路径 |
| 网络路由 | OSPF协议 | 计算最短路径，分布式实现 |
| 游戏开发 | NPC寻路 | 网格地图上的最短路径 |
| 电路设计 | 信号延迟最小化 | 传播延迟建模为非负权重 |

---

## 八、多维对比

| 算法 | 时间复杂度 | 负权边 | 全源 | 适用场景 |
|------|------------|--------|------|----------|
| Dijkstra | O((V+E)logV) | 否 | 否 | 非负权重单源 |
| Bellman-Ford | O(VE) | 是 | 否 | 含负权边 |
| Floyd-Warshall | O(V³) | 是 | 是 | 稠密图全源 |

---

## 九、扩展阅读

| 教材 | 章节 | 推荐度 |
|------|------|--------|
| CLRS | 第24章 | ⭐⭐⭐⭐⭐ |
| 算法导论 | 第24章 | ⭐⭐⭐⭐⭐ |

---

## 十、修订历史

| 版本 | 日期 | 修订内容 |
|------|------|----------|
| v1.0 | 2026-04-09 | 初始版本 |

---

**标签**: #最短路径 #Dijkstra #贪心算法 #图算法

**相关笔记**:
- [图遍历.md](./图遍历.md)
- [贪心算法.md](./贪心算法.md)
- [最小生成树.md](./最小生成树.md)
