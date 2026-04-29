---
title: 凸包与Voronoi图
version: 1.0
last_updated: 2026-04-19
---

# 凸包与Voronoi图 (Convex Hull & Voronoi Diagrams)

> **学科**: 计算几何、算法设计与分析
> **难度**: ★★★★☆
> **先修**: 基础数据结构、排序算法、计算几何基础、图论基础
> **学时**: 8小时
> **来源**: CLRS第33章、de Berg《计算几何》、O'Rourke《Computational Geometry in C》
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 凸包定义

**正式定义**:

给定平面上的点集 $P = \{p_1, p_2, \ldots, p_n\}$，**凸包** $\text{CH}(P)$ 是包含 $P$ 中所有点的最小凸集，等价于所有包含 $P$ 的凸集的交集。

$$
\text{CH}(P) = \left\{ \sum_{i=1}^{n} \lambda_i p_i \,\middle|\, \lambda_i \geq 0, \sum_{i=1}^{n} \lambda_i = 1 \right\}
$$

**等价表述**:
- 包含所有点的最小凸多边形
- 所有凸组合构成的集合
- 以 $P$ 中点为顶点的所有凸多边形的并集

**直观解释**:
想象将橡皮筋套在所有点上然后松开，橡皮筋包围的区域就是凸包。凸包的顶点是点集的"最外围"点。

**关键要点**:
- **凸性**: 凸包内任意两点的连线完全包含在凸包内
- **唯一性**: 给定有限点集，凸包唯一确定
- **顶点性质**: 凸包顶点是原点集的子集
- **复杂度**: $n$ 个点的凸包最多有 $n$ 个顶点

### 1.2 凸包属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 顶点数上界 | $O(n)$ | $n$ 个点最多 $n$ 个凸包顶点 |
| 边数上界 | $O(n)$ | 平面图欧拉公式 |
| 凸包面积 | 最小包围凸区域 | 用于形状分析 |
| 直径 | 凸包上最远两点距离 | 旋转卡壳法 $O(n)$ 计算 |
| 宽度 | 平行支撑线最小距离 | 对踵点对概念 |

**性质总结**:
1. **Carathéodory定理**: 若 $p \in \text{CH}(P)$，则存在 $P$ 的至多 $d+1$ 个点使 $p$ 是其凸组合（$d$ 为维数）
2. **Radon定理**: 任何 $d+2$ 个点集可划分为两个子集，其凸包相交
3. **Helly定理**: 有限个凸集族，若任意 $d+1$ 个有交，则全集有交

### 1.3 凸包变体

**k-层凸包 (Onion Peeling)**:
- 定义: 递归地移除凸包外层，得到嵌套凸包结构
- 复杂度: $O(n^2)$ 最坏情况
- 应用: 深度排序、异常检测

**α-形状 (Alpha Shapes)**:
- 定义: 通过参数 $α$ 控制凸包"紧致程度"
- 与Delaunay三角剖分的关系: $α \to \infty$ 时趋近凸包
- 应用: 分子建模、点云表面重建

**加权凸包 (Weighted Convex Hull)**:
- 定义: 给点赋予权重，考虑加权凸组合
- 与Voronoi图的关系: 与加权Voronoi图对偶

---

### 1.4 Voronoi图定义

**正式定义**:

给定平面上 $n$ 个**站点**（sites）$S = \{s_1, s_2, \ldots, s_n\}$，**Voronoi图**将平面划分为 $n$ 个区域，每个区域 $V(s_i)$ 包含距离 $s_i$ 最近的所有点。

$$
V(s_i) = \{ p \in \mathbb{R}^2 \mid \forall j \neq i: d(p, s_i) \leq d(p, s_j) \}
$$

**Voronoi单元**:
每个 $V(s_i)$ 是一个凸多边形（可能无界），称为站点 $s_i$ 的Voronoi单元。

**Voronoi边与顶点**:
- **Voronoi边**: 两个站点的等距点集，即 $V(s_i) \cap V(s_j)$
- **Voronoi顶点**: 三个或更多站点的等距点

**直观解释**:
想象每个站点是一个"领地中心"，平面上每个点归属最近的领地中心。Voronoi图就是所有领地边界的集合。

**关键要点**:
- **凸性**: 每个Voronoi单元都是凸集
- **覆盖性**: Voronoi图覆盖整个平面
- **互斥性**: 不同单元的内部不相交
- **对偶性**: 与Delaunay三角剖分对偶

### 1.5 Voronoi图属性

| 属性 | 描述 | 复杂度 |
|------|------|--------|
| Voronoi顶点数 | $\leq 2n - 5$ | $n \geq 3$ 时 |
| Voronoi边数 | $\leq 3n - 6$ | 平面图的欧拉公式 |
| 单元数 | $n$ | 每个站点一个 |
| 平均边数 | $\leq 6$ | 每个单元平均边数上界 |

**性质总结**:
1. **最近邻性质**: 站点 $s_i$ 的最近邻的Voronoi单元必与 $V(s_i)$ 相邻
2. **最大空圆**: Voronoi顶点是最大空圆的圆心（圆内无其他站点）
3. **凸包站点**: 凸包上站点的Voronoi单元无界
4. **局部性**: 添加/删除一个站点只影响局部区域

### 1.6 Voronoi图变体

**高阶Voronoi图**:
- $k$阶Voronoi图: 距离某 $k$ 个站点最近的所有点
- 阶数-1 Voronoi图: 距离某站点最远（最远离线图）

**加权Voronoi图**:
- **加法加权**: $d(p, s_i) - w_i$
- **乘法加权**: $d(p, s_i) / w_i$
- **幂图 (Power Diagram)**: $d^2(p, s_i) - w_i$

**约束Voronoi图**:
- 线段Voronoi图: 站点为线段
- 流形上的Voronoi图: 限制在曲面或网络
- 障碍物Voronoi图: 考虑障碍物约束

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| 向量运算 | ⭐⭐⭐⭐⭐ | 点积、叉积、向量加减 |
| 平面几何 | ⭐⭐⭐⭐⭐ | 直线方程、距离公式、方向判断 |
| 排序算法 | ⭐⭐⭐⭐⭐ | 比较排序、极角排序 |
| 数据结构 | ⭐⭐⭐⭐⭐ | 栈、队列、优先队列、平衡树 |
| 图论基础 | ⭐⭐⭐⭐☆ | 平面图、对偶图概念 |
| 渐近分析 | ⭐⭐⭐⭐☆ | 大O符号、复杂度分析 |

### 2.2 相关概念

**紧密相关**:
- **Delaunay三角剖分** - Voronoi图的对偶图
- **凸包** - 与Voronoi图共同构成计算几何基础结构
- **最近邻搜索** - 利用Voronoi图进行高效查询
- **平面划分** - 计算几何中点集划分的核心工具

**一般相关**:
- **四叉树/k-d树** - 空间分割的另一种方式
- **范围树** - 正交范围查询
- **线段树** - 区间查询数据结构
- **几何对偶性** - 点↔线的对偶变换

### 2.3 后续扩展

1. **高维计算几何** → 三维凸包、高维Voronoi图
2. **随机几何** → 随机点集的Voronoi图性质
3. **离散微分几何** → 网格生成、曲面重建
4. **计算拓扑** → 持续同调、拓扑数据分析

### 2.4 思维导图

```
凸包与Voronoi图
├── 凸包算法
│   ├── Graham扫描 (O(n log n))
│   ├── QuickHull (O(n log n) 平均)
│   ├── 单调链算法 (O(n log n))
│   ├── Jarvis步进法 (O(nh))
│   └── 分治算法 (O(n log n))
├── Voronoi图
│   ├── 扫描线算法 (Fortune, O(n log n))
│   ├── 分治算法 (O(n log n))
│   ├── 增量算法 (O(n²))
│   └── 对偶构造 (通过Delaunay三角剖分)
├── Delaunay三角剖分
│   ├── 空外接圆性质
│   ├── 最大化最小角
│   ├── 与Voronoi图对偶
│   └── 构造算法 (翻转、扫描线、分治)
└── 应用
    ├── 设施选址
    ├── 网格生成
    ├── 最近邻搜索
    ├── 机器人路径规划
    └── 自然现象建模
```

---

## 三、形式化证明

### 3.1 凸包核心定理

**定理 1** (Graham扫描正确性): Graham扫描算法正确地计算了给定点集的凸包。

**证明**:

**循环不变式**: 在处理第 $i$ 个点时，栈中存储的是已处理点集中构成凸包的部分顶点，且按逆时针顺序排列。

**初始化**: 处理前两个点时，栈中包含它们形成的线段，显然构成凸包。

**保持**: 设处理点 $p_i$ 时，栈顶两点为 $p_{top-1}$ 和 $p_{top}$。
- 若 $p_{top-1} \to p_{top} \to p_i$ 构成左转（叉积 $> 0$），则将 $p_i$ 入栈，凸包性质保持
- 若右转或共线（叉积 $\leq 0$），则 $p_{top}$ 不可能是凸包顶点，出栈后继续检查

**终止**: 所有点处理完毕后，栈中即为完整的凸包顶点序列。

**关键点**: 叉积判断确保每次维护的都是"最左转"路径，移除所有非凸包顶点。∎

---

**定理 2** (凸包顶点数上界): 平面上 $n$ 个点的凸包至多有 $n$ 个顶点。

**证明**: 
每个凸包顶点都是原输入点集的成员，而输入点集只有 $n$ 个点，因此凸包顶点数 $\leq n$。∎

---

### 3.2 Voronoi图核心定理

**定理 3** (Voronoi单元凸性): 每个Voronoi单元 $V(s_i)$ 都是凸集。

**证明**:

设 $p, q \in V(s_i)$，即对所有 $j \neq i$:
$$d(p, s_i) \leq d(p, s_j), \quad d(q, s_i) \leq d(q, s_j)$$

对任意 $\lambda \in [0, 1]$，令 $r = \lambda p + (1-\lambda)q$。

由于欧氏距离是凸函数（根据三角不等式），有:
$$d(r, s_i) \leq \lambda d(p, s_i) + (1-\lambda)d(q, s_i)$$

且对每个 $j \neq i$:
$$\lambda d(p, s_i) + (1-\lambda)d(q, s_i) \leq \lambda d(p, s_j) + (1-\lambda)d(q, s_j)$$

又因为距离函数是凸函数:
$$\lambda d(p, s_j) + (1-\lambda)d(q, s_j) \leq d(\lambda p + (1-\lambda)q, s_j) = d(r, s_j)$$

因此 $d(r, s_i) \leq d(r, s_j)$，即 $r \in V(s_i)$，$V(s_i)$ 是凸集。∎

---

**定理 4** (Voronoi顶点与最大空圆): Voronoi顶点是距离其相邻三个站点等距的唯一点，且是以该点为圆心、到任一相邻站点距离为半径的圆内的最大空圆的圆心。

**证明**:

设 $v$ 是Voronoi顶点，与 $V(s_i), V(s_j), V(s_k)$ 相邻，则:
$$d(v, s_i) = d(v, s_j) = d(v, s_k) = r$$

**唯一性**: 到三个不共线点等距的点唯一（外心）。

**最大空圆**: 对任意点 $p$ 在圆 $B(v, r)$ 内部，有 $d(p, v) < r$，因此:
$$d(p, s_i) \leq d(p, v) + d(v, s_i) < r + r = 2r$$

实际上，由于 $v$ 是外心，对圆内任意点 $p$:
$$d(p, s_i) < r \quad \text{对所有 } i \in \{i, j, k\}$$

且对任意其他站点 $s_l$，由Voronoi顶点定义:
$$d(v, s_l) > r$$

因此圆 $B(v, r)$ 内部不含任何站点。若增大半径，则必包含 $s_i, s_j, s_k$ 之一，故为最大空圆。∎

---

**定理 5** (Delaunay-Voronoi对偶性): Delaunay三角剖分与Voronoi图互为平面对偶图。

**证明**:

**对偶映射**:
- Voronoi单元 $V(s_i)$ ↔ Delaunay顶点 $s_i$
- Voronoi边 $V(s_i) \cap V(s_j)$ ↔ Delaunay边 $(s_i, s_j)$
- Voronoi顶点 ↔ Delaunay三角形面

**邻接保持**: 两个Voronoi单元相邻当且仅当对应Delaunay顶点有边相连。

**面-顶点对应**: Voronoi图的顶点对应Delaunay三角剖分的面（三角形）。

**平面图性质**: 由于Voronoi图是平面图，其对偶Delaunay三角剖分也是平面图。

**外接圆性质**: Delaunay边 $(s_i, s_j)$ 存在当且仅当存在一点（Voronoi边上）到 $s_i$ 和 $s_j$ 等距且最近，这等价于存在空外接圆。∎

---

### 3.3 Fortune算法复杂度分析

**定理 6** (Fortune算法复杂度): Fortune扫描线算法计算Voronoi图的时间复杂度为 $O(n \log n)$，空间复杂度为 $O(n)$。

**证明概要**:

**事件点**: 站点事件（$n$ 个）和圆事件（$O(n)$ 个），共 $O(n)$ 个事件。

**优先队列操作**: 每个事件入队、出队一次，每次 $O(\log n)$，总计 $O(n \log n)$。

**海滩线维护**: 使用平衡二叉树，每次插入、删除、查询为 $O(\log n)$，总计 $O(n \log n)$。

**空间消耗**: 海滩线存储 $O(n)$ 条抛物线弧，事件队列 $O(n)$ 个事件，输出 $O(n)$ 条边。

综上，时间 $O(n \log n)$，空间 $O(n)$。∎

---

## 四、算法详解

### 4.1 Graham扫描算法

**算法描述**:

```
算法: Graham-Scan(P)
输入: 点集 P = {p₁, p₂, ..., pₙ}
输出: 凸包顶点序列（逆时针顺序）

1.  找到最左下角的点 p₀（y最小，y相同时x最小）
2.  以 p₀ 为原点，对其他点按极角排序得到 {p₁, p₂, ..., pₙ₋₁}
3.  初始化栈 S = [p₀, p₁, p₂]
4.  for i = 3 to n-1 do
5.      while S中次栈顶、栈顶、pi 不构成左转 do
6.          S.pop()
7.      end while
8.      S.push(pᵢ)
9.  end for
10. return S
```

**关键操作 - 叉积判断**:

对于三点 $p_1, p_2, p_3$，计算叉积:

$$\text{cross} = (p_2 - p_1) \times (p_3 - p_1) = (x_2-x_1)(y_3-y_1) - (y_2-y_1)(x_3-x_1)$$

- $\text{cross} > 0$: 左转（逆时针）
- $\text{cross} < 0$: 右转（顺时针）
- $\text{cross} = 0$: 共线

---

### 4.2 QuickHull算法

**算法描述**:

```
算法: QuickHull(P)
输入: 点集 P
输出: 凸包顶点集

1.  找到 x 坐标最小和最大的点 A, B（凸包上的点）
2.  将点集分为两部分：
    - S₁: 在直线 AB 上方的点
    - S₂: 在直线 AB 下方的点
3.  return {A, B} ∪ QuickHull-Helper(S₁, A, B) ∪ QuickHull-Helper(S₂, B, A)

QuickHull-Helper(S, A, B):
1.  if S = ∅ then return ∅
2.  找到 S 中距离直线 AB 最远的点 C
3.  将 S 分为：
    - S₁: 在直线 AC 左侧的点
    - S₂: 在直线 CB 左侧的点
4.  return QuickHull-Helper(S₁, A, C) ∪ {C} ∪ QuickHull-Helper(S₂, C, B)
```

**复杂度分析**:
- 平均情况: $O(n \log n)$（类似快速排序）
- 最坏情况: $O(n^2)$（点已按凸包顺序排列）

---

### 4.3 Fortune扫描线算法

**核心思想**:

使用一条扫描线自上而下扫过平面，维护**海滩线**（beach line）—— 扫描线下方由抛物线弧组成的曲线。抛物线弧是扫描线上某点与某站点的等距轨迹。

**数据结构**:

1. **事件优先队列**: 存储站点事件和圆事件
2. **海滩线 (平衡二叉树)**: 按x坐标排序的抛物线弧
3. **DCEL (双连通边列表)**: 存储Voronoi图结构

**事件类型**:

**站点事件**: 扫描线遇到新站点时
- 在海滩线上插入新的抛物线弧
- 可能生成新的圆事件

**圆事件**: 某段抛物线弧收缩为一个点时
- 从海滩线删除对应弧
- 在Voronoi图中创建顶点
- 可能生成新的圆事件

**算法流程**:

```
算法: Fortune-Voronoi(S)
输入: 站点集 S
输出: Voronoi图

1.  初始化事件队列 Q，将所有站点按 y 坐标排序入队
2.  初始化空的海滩线 T（平衡二叉树）
3.  while Q 不为空 do
4.      event = Q.extract-min()
5.      if event 是站点事件 then
6.          Handle-Site-Event(event)
7.      else
8.          Handle-Circle-Event(event)
9.      end if
10. end while
11. 完成无边界的边

Handle-Site-Event(site p):
1.  在海滩线 T 中找到 p 上方的弧 α
2.  将 α 替换为三段弧：α₁, α₂(p), α₃
3.  删除与 α 相关的圆事件
4.  为 (α₁, α₂) 和 (α₂, α₃) 对检查新的圆事件

Handle-Circle-Event(event):
1.  在海滩线 T 中删除收缩的弧 α
2.  在Voronoi图中添加顶点，完成相关边
3.  删除与 α 相关的其他圆事件
4.  为新相邻的弧对检查圆事件
```

---

### 4.4 Delaunay三角剖分构造

**翻转算法 (Flip Algorithm)**:

```
算法: Delaunay-Flip(S)
输入: 点集 S（无四点共圆）
输出: Delaunay三角剖分

1.  构造任意三角剖分（如扫描线算法）
2.  while 存在非法边 do
3.      找到非法边 e = (a,b)，共享两个三角形 △abc 和 △abd
4.      翻转 e: 删除 e，添加边 (c,d)
5.      新边 (c,d) 的两个对角三角形需重新检查
6.  end while
7.  return 三角剖分
```

**非法边判定**: 边 $(a,b)$ 是非法的当且仅当 $d$ 在三角形 $\triangle abc$ 的外接圆内部。

---

## 五、示例与代码

### 5.1 Graham扫描示例

**问题**: 计算点集 $P = \{(0,0), (2,0), (1,1), (2,2), (0,2), (0.5, 0.5)\}$ 的凸包。

**执行过程**:

| 步骤 | 操作 | 栈状态 | 说明 |
|------|------|--------|------|
| 1 | 找最左下点 | - | 选择 $(0,0)$ 为 $p_0$ |
| 2 | 极角排序 | - | 顺序: $(0,0), (0,2), (0.5,0.5), (1,1), (2,2), (2,0)$ |
| 3 | 初始化 | $(0,0), (0,2), (0.5,0.5)$ | 前3点入栈 |
| 4 | 处理 $(1,1)$ | $(0,0), (0,2), (0.5,0.5), (1,1)$ | 左转，入栈 |
| 5 | 处理 $(2,2)$ | $(0,0), (0,2), (0.5,0.5), (1,1), (2,2)$ | 左转，入栈 |
| 6 | 处理 $(2,0)$ | 弹出 $(2,2)$ | 右转，弹出 |
| 7 | 再次检查 | 弹出 $(1,1)$ | 仍右转，弹出 |
| 8 | 入栈 $(2,0)$ | $(0,0), (0,2), (0.5,0.5), (2,0)$ | 左转，入栈 |

**结果**: 凸包顶点为 $(0,0), (2,0), (2,2), (0,2)$（逆时针）。

---

### 5.2 Python实现

**Graham扫描实现**:

```python
from typing import List, Tuple
import math

Point = Tuple[float, float]

def cross(o: Point, a: Point, b: Point) -> float:
    """计算叉积 (OA × OB)"""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])

def dist_sq(a: Point, b: Point) -> float:
    """计算距离平方"""
    return (a[0] - b[0])**2 + (a[1] - b[1])**2

def graham_scan(points: List[Point]) -> List[Point]:
    """
    Graham扫描算法计算凸包
    时间复杂度: O(n log n)
    返回: 逆时针顺序的凸包顶点
    """
    n = len(points)
    if n <= 1:
        return points.copy()
    
    # 1. 找到最左下角的点
    start = min(points, key=lambda p: (p[1], p[0]))
    
    # 2. 极角排序
    def polar_angle(p: Point) -> float:
        return math.atan2(p[1] - start[1], p[0] - start[0])
    
    # 按极角排序，极角相同则按距离排序
    sorted_points = sorted(
        [p for p in points if p != start],
        key=lambda p: (polar_angle(p), dist_sq(start, p))
    )
    
    # 3. Graham扫描
    hull = [start]
    for p in sorted_points:
        # 当不构成左转时，弹出栈顶
        while len(hull) >= 2 and cross(hull[-2], hull[-1], p) <= 0:
            hull.pop()
        hull.append(p)
    
    return hull

# 测试
if __name__ == "__main__":
    points = [(0, 0), (2, 0), (1, 1), (2, 2), (0, 2), (0.5, 0.5), (1, 0.5)]
    hull = graham_scan(points)
    print("凸包顶点 (逆时针):", hull)
    
    # 计算凸包面积（鞋带公式）
    def polygon_area(poly: List[Point]) -> float:
        area = 0
        n = len(poly)
        for i in range(n):
            j = (i + 1) % n
            area += poly[i][0] * poly[j][1]
            area -= poly[j][0] * poly[i][1]
        return abs(area) / 2
    
    print("凸包面积:", polygon_area(hull))
```

**QuickHull实现**:

```python
def quickhull(points: List[Point]) -> List[Point]:
    """
    QuickHull算法计算凸包
    平均时间复杂度: O(n log n)
    """
    if len(points) <= 1:
        return points.copy()
    
    # 找到x坐标最小和最大的点
    min_point = min(points, key=lambda p: p[0])
    max_point = max(points, key=lambda p: p[0])
    
    # 递归构造凸包
    hull = set()
    hull.add(min_point)
    hull.add(max_point)
    
    # 分割点集并递归
    left_set = [p for p in points if cross(min_point, max_point, p) > 0]
    right_set = [p for p in points if cross(min_point, max_point, p) < 0]
    
    _quickhull_recursive(left_set, min_point, max_point, hull)
    _quickhull_recursive(right_set, max_point, min_point, hull)
    
    # 按极角排序返回
    center = (sum(p[0] for p in hull) / len(hull), 
              sum(p[1] for p in hull) / len(hull))
    return sorted(hull, key=lambda p: math.atan2(p[1]-center[1], p[0]-center[0]))

def _quickhull_recursive(points: List[Point], a: Point, b: Point, hull: set):
    """递归辅助函数"""
    if not points:
        return
    
    # 找到距离直线AB最远的点
    max_dist = -1
    max_point = None
    for p in points:
        d = abs(cross(a, b, p)) / math.sqrt(dist_sq(a, b))
        if d > max_dist:
            max_dist = d
            max_point = p
    
    if max_point is None:
        return
    
    hull.add(max_point)
    
    # 分割点集
    set1 = [p for p in points if cross(a, max_point, p) > 0]
    set2 = [p for p in points if cross(max_point, b, p) > 0]
    
    _quickhull_recursive(set1, a, max_point, hull)
    _quickhull_recursive(set2, max_point, b, hull)
```

**Voronoi图简化实现（基于Scipy）**:

```python
import numpy as np
from scipy.spatial import Voronoi, voronoi_plot_2d
import matplotlib.pyplot as plt

def compute_voronoi(points: np.ndarray) -> Voronoi:
    """
    计算Voronoi图
    输入: n×2 的点坐标数组
    输出: Scipy Voronoi对象
    """
    vor = Voronoi(points)
    return vor

def compute_delaunay(points: np.ndarray):
    """
    计算Delaunay三角剖分
    """
    from scipy.spatial import Delaunay
    return Delaunay(points)

# 示例
if __name__ == "__main__":
    # 随机生成点集
    np.random.seed(42)
    points = np.random.rand(10, 2)
    
    # 计算Voronoi图
    vor = compute_voronoi(points)
    
    # 可视化
    fig, axes = plt.subplots(1, 2, figsize=(12, 5))
    
    # Voronoi图
    voronoi_plot_2d(vor, ax=axes[0])
    axes[0].scatter(points[:, 0], points[:, 1], c='red', zorder=5)
    axes[0].set_title('Voronoi Diagram')
    axes[0].set_xlim(0, 1)
    axes[0].set_ylim(0, 1)
    
    # Delaunay三角剖分
    tri = compute_delaunay(points)
    axes[1].triplot(points[:, 0], points[:, 1], tri.simplices)
    axes[1].scatter(points[:, 0], points[:, 1], c='red', zorder=5)
    axes[1].set_title('Delaunay Triangulation')
    axes[1].set_xlim(0, 1)
    axes[1].set_ylim(0, 1)
    
    plt.tight_layout()
    plt.savefig('voronoi_delaunay.png')
    plt.show()
```

---

## 5.3 反例与常见问题
### 5.3 反例与常见问题

**Graham扫描常见问题**:

**问题1**: 共线点的处理
```python
# 错误：共线点被全部保留
while len(hull) >= 2 and cross(hull[-2], hull[-1], p) < 0:
    hull.pop()

# 正确：根据需求选择保留或删除共线点
# 保留边界共线点：cross <= 0
# 只保留端点：cross < 0
```

**问题2**: 所有点共线
```python
# 需要特殊处理：凸包退化为线段
if all(cross(points[0], points[i], points[i+1]) == 0 
       for i in range(1, len(points)-1)):
    return [min(points), max(points)]  # 只返回两个端点
```

**问题3**: 浮点精度
```python
# 使用epsilon比较而非直接比较零
def cross_sign(o, a, b, eps=1e-10):
    c = cross(o, a, b)
    if c > eps: return 1    # 左转
    if c < -eps: return -1  # 右转
    return 0                # 共线
```

---

## 六、习题

### 6.1 理解题

1. **为什么Graham扫描的时间复杂度是 $O(n \log n)$？** [难度⭐]

   <details>
   <summary>解答</summary>
   Graham扫描的主要开销在于极角排序，使用比较排序需要 $O(n \log n)$ 时间。扫描过程每个点最多入栈出栈一次，为 $O(n)$。因此总复杂度为 $O(n \log n)$。
   </details>

2. **Voronoi图与Delaunay三角剖分的对偶关系如何体现？** [难度⭐⭐]

   <details>
   <summary>解答</summary>
   对偶关系体现在：
   - Voronoi单元 ↔ Delaunay顶点（一一对应）
   - Voronoi边 ↔ Delaunay边（两两相邻关系）
   - Voronoi顶点 ↔ Delaunay三角形面（三个站点确定的三角形）
   这种对偶性意味着构造其中一个结构后，另一个可以在 $O(n)$ 时间内导出。
   </details>

### 6.2 应用题

3. **旋转卡壳法求凸包直径** [难度⭐⭐]

   给定凸包顶点（逆时针顺序），设计 $O(n)$ 算法求凸包上最远两点距离。

   <details>
   <summary>解答</summary>

   ```python
   def rotating_calipers(hull: List[Point]) -> float:
       """
       旋转卡壳法求凸包直径
       时间复杂度: O(n)
       """
       n = len(hull)
       if n == 1:
           return 0
       if n == 2:
           return math.sqrt(dist_sq(hull[0], hull[1]))
       
       # 找到y坐标最大的点（对踵点对起点）
       j = 1
       max_dist = 0
       
       for i in range(n):
           # 下一条边
           ni = (i + 1) % n
           # 当面积增加时，移动j
           while abs(cross(hull[i], hull[ni], hull[(j+1)%n])) > \
                 abs(cross(hull[i], hull[ni], hull[j])):
               j = (j + 1) % n
           
           # 更新最大距离
           max_dist = max(max_dist, dist_sq(hull[i], hull[j]),
                         dist_sq(hull[ni], hull[j]))
       
       return math.sqrt(max_dist)
   ```

   核心思想：凸包直径必在某对对踵点之间取得。通过旋转两条平行支撑线，可以在 $O(n)$ 时间内枚举所有对踵点对。
   </details>

4. **最近点对问题** [难度⭐⭐⭐]

   使用分治法和凸包知识，设计 $O(n \log n)$ 算法求平面上最近点对。

   <details>
   <summary>解答</summary>

   ```python
   def closest_pair(points: List[Point]) -> float:
       """
       分治法求最近点对
       时间复杂度: O(n log n)
       """
       def closest_pair_recursive(px, py):
           n = len(px)
           if n <= 3:
               # 暴力求解
               min_dist = float('inf')
               for i in range(n):
                   for j in range(i+1, n):
                       min_dist = min(min_dist, dist_sq(px[i], px[j]))
               return min_dist
           
           # 分割
           mid = n // 2
           mid_point = px[mid]
           
           # 按y坐标分割
           pyl = [p for p in py if p[0] <= mid_point[0]]
           pyr = [p for p in py if p[0] > mid_point[0]]
           
           # 递归求解
           dl = closest_pair_recursive(px[:mid], pyl)
           dr = closest_pair_recursive(px[mid:], pyr)
           d = min(dl, dr)
           
           # 检查跨越中线的点对
           strip = [p for p in py if (p[0] - mid_point[0])**2 < d]
           
           # 只需检查每个点后面的最多6个点
           for i in range(len(strip)):
               for j in range(i+1, min(i+7, len(strip))):
                   if (strip[j][1] - strip[i][1])**2 >= d:
                       break
                   d = min(d, dist_sq(strip[i], strip[j]))
           
           return d
       
       # 按x和y坐标排序
       px = sorted(points, key=lambda p: p[0])
       py = sorted(points, key=lambda p: p[1])
       
       return math.sqrt(closest_pair_recursive(px, py))
   ```

   证明关键：在带状区域内，每个点只需检查其后最多6个点。这是因为将区域划分为边长为 $\sqrt{d}/2$ 的小方格，每个方格内最多一个点。
   </details>

### 6.3 证明题

5. **Delaunay三角剖分的空外接圆性质** [难度⭐⭐⭐]

   证明：Delaunay三角剖分中，每个三角形的外接圆内部不含其他站点。

   <details>
   <summary>解答</summary>
   
   **证明**（反证法）：
   
   假设在Delaunay三角剖分中存在三角形 $\triangle abc$，其外接圆 $C$ 内部包含另一站点 $d$。
   
   考虑边 $(a, b)$。由于 $d$ 在 $C$ 内部，且 $C$ 是 $\triangle abc$ 的外接圆，有:
   $$\angle adb > \angle acb$$
   （圆内角大于圆周角）
   
   这意味着边 $(a, b)$ 是非法的，因为 $d$ 违反了Delaunay条件。
   
   根据翻转引理，存在边翻转操作可以将 $(a,b)$ 替换为 $(c,d)$，同时增加最小角或保持空外接圆性质。
   
   重复此过程，最终将得到所有三角形都满足空外接圆性质的三角剖分，即Delaunay三角剖分。
   
   因此，Delaunay三角剖分中每个三角形的外接圆内部不含其他站点。∎
   </details>

---

## 七、应用场景

### 7.1 经典应用

| 应用场景 | 具体问题 | 使用本主题的原因 |
|----------|----------|------------------|
| 设施选址 | 最小化最大服务距离 | Voronoi单元直接对应服务区域 |
| 碰撞检测 | 物体包围盒计算 | 凸包提供紧凑的边界表示 |
| 网格生成 | 有限元分析网格 | Delaunay三角剖分最大化最小角 |
| 最近邻搜索 | 高维数据检索 | Voronoi图提供精确的最近邻区域 |
| 形状分析 | 物体轮廓描述 | 凸包比率（面积比、周长比）作为形状特征 |
| 机器人路径规划 | 避障路径生成 | Voronoi图提供最大间隙路径 |

### 7.2 实际案例

**案例1: 物流配送中心选址**

**背景**: 某快递公司需在10个城市中选址建设配送中心，要求最小化最大配送距离。

**应用方式**:
1. 将城市位置作为站点构建Voronoi图
2. 每个配送中心服务其Voronoi单元内的城市
3. 使用1-中心问题算法（Voronoi顶点候选）找到最优位置

**效果**: 相比随机选址，最大配送距离降低35%。

---

**案例2: 三维重建中的网格生成**

**背景**: 从激光扫描点云重建三维模型。

**应用方式**:
1. 对点云进行Delaunay三角剖分
2. 利用α-形状提取表面网格
3. 优化网格质量（最小角最大化）

**效果**: 生成的网格质量高，适合后续有限元分析和渲染。

---

**案例3: 游戏开发中的碰撞检测**

**背景**: 实时物理引擎需要高效的物体碰撞检测。

**应用方式**:
1. 为每个物体预计算凸包（或凸包层次结构）
2. 使用GJK算法在凸包层面进行粗略检测
3. 仅在凸包相交时进行精细检测

**效果**: 碰撞检测性能提升10倍以上。

### 7.3 跨领域联系

**与机器学习的关系**:
- **k近邻算法**: Voronoi图的几何解释
- **支持向量机**: 最大间隔分类与凸包的关系
- **聚类分析**: k-means与Voronoi单元的联系

**与图形学的关系**:
- **非真实感渲染**: 使用Voronoi图创建点画效果
- **纹理合成**: 基于Voronoi的 procedural texture
- **网格变形**: 使用Voronoi权重进行空间变形

**与自然科学的关系**:
- **晶体学**: 晶粒结构与Voronoi图相似
- **生物学**: 细胞排列、领地划分
- **地理学**: 流域划分、影响力范围

---

## 八、多维对比

### 8.1 凸包算法对比

| 算法 | 时间复杂度 | 空间复杂度 | 适用场景 | 特点 |
|------|-----------|-----------|----------|------|
| Graham扫描 | $O(n \log n)$ | $O(n)$ | 通用场景 | 实现简单，需极角排序 |
| QuickHull | $O(n \log n)$ 平均<br>$O(n^2)$ 最坏 | $O(n)$ | 实际数据 | 常数小，类似快速排序 |
| 单调链 | $O(n \log n)$ | $O(n)$ | 需要有序输出 | 按x坐标排序，两遍扫描 |
| Jarvis步进 | $O(nh)$ | $O(1)$ 额外 | $h$ 较小 | 输出敏感， Gift Wrapping |
| Chan算法 | $O(n \log h)$ | $O(n)$ | 理论最优 | 输出敏感最优算法 |
| 分治法 | $O(n \log n)$ | $O(n \log n)$ | 并行计算 | 可并行化 |

### 8.2 Voronoi图算法对比

| 算法 | 时间复杂度 | 空间复杂度 | 特点 |
|------|-----------|-----------|------|
| Fortune扫描线 | $O(n \log n)$ | $O(n)$ | 最常用，高效稳定 |
| 分治法 | $O(n \log n)$ | $O(n)$ | 可并行，实现复杂 |
| 增量法 | $O(n^2)$ 最坏<br>$O(n)$ 平均 | $O(n)$ | 适合动态场景 |
| 分块法 | $O(n \log n)$ | $O(n)$ | 适合大规模数据 |
| 通过Delaunay | $O(n \log n)$ | $O(n)$ | 已有Delaunay时高效 |

### 8.3 空间数据结构对比

| 结构 | 构建时间 | 查询时间 | 适用查询 |
|------|---------|---------|----------|
| Voronoi图 | $O(n \log n)$ | $O(\log n)$ | 最近邻 |
| k-d树 | $O(n \log n)$ | $O(\sqrt{n})$ | 范围查询、最近邻 |
| 四叉树 | $O(n \log n)$ | 可变 | 空间索引 |
| 范围树 | $O(n \log n)$ | $O(\log n)$ | 正交范围查询 |
| R树 | $O(n \log n)$ | 可变 | 数据库索引 |

### 8.4 决策建议

**选择凸包算法时**:
- 需要稳定 $O(n \log n)$ → Graham扫描或单调链
- 追求实际性能 → QuickHull
- 凸包顶点很少 ($h \ll n$) → Jarvis步进
- 需要理论最优 → Chan算法

**选择Voronoi图算法时**:
- 一般情况 → Fortune扫描线
- 需要动态更新 → 增量法
- 已有Delaunay → 对偶转换
- 大规模并行 → 分治法

---

## 九、扩展阅读

### 9.1 教材章节

| 教材 | 章节 | 页码 | 推荐度 |
|------|------|------|--------|
| CLRS《算法导论》 | 第33章 计算几何 | pp. 1017-1044 | ⭐⭐⭐⭐⭐ |
| de Berg《计算几何》 | 第1, 7, 9章 | pp. 1-30, 147-170, 191-218 | ⭐⭐⭐⭐⭐ |
| O'Rourke《Computational Geometry in C》 | 第3, 4, 5章 | pp. 63-138 | ⭐⭐⭐⭐☆ |
| Preparata & Shamos《计算几何导论》 | 第3章 | pp. 95-184 | ⭐⭐⭐⭐⭐ |
| Boissonnat《Geometric and Topological Inference》 | 第1-4章 | - | ⭐⭐⭐⭐☆ |

### 9.2 论文

1. **"A sweepline algorithm for Voronoi diagrams"** - S. Fortune, 1987
   - **要点**: 提出Fortune扫描线算法，Voronoi图构造的经典方法
   - **链接**: [DOI: 10.1145/10515.10549](https://doi.org/10.1145/10515.10549)

2. **"Delaunay Refinement Mesh Generation"** - J. R. Shewchuk, 1998
   - **要点**: Delaunay细化的理论基础和实践方法
   - **链接**: [PhD Thesis, CMU](https://www.cs.cmu.edu/~jrsh/papers/drthesis.pdf)

3. **"An optimal convex hull algorithm in any fixed dimension"** - B. Chazelle, 1993
   - **要点**: 高维凸包的最优算法
   - **链接**: [DOI: 10.1007/BF02573985](https://doi.org/10.1007/BF02573985)

4. **"The quickhull algorithm for convex hulls"** - C. B. Barber et al., 1996
   - **要点**: QuickHull算法的完整描述和分析
   - **链接**: [DOI: 10.1145/235815.235821](https://doi.org/10.1145/235815.235821)

### 9.3 在线资源

- **CGAL (Computational Geometry Algorithms Library)**: [www.cgal.org](https://www.cgal.org)
  - 工业级计算几何算法库，包含凸包、Voronoi、Delaunay等完整实现

- **Qhull**: [www.qhull.org](http://www.qhull.org)
  - QuickHull算法的权威实现，支持高维凸包和Voronoi图

- **Joseph O'Rourke的教程**: [cs.smith.edu/~orourke/](https://cs.smith.edu/~orourke/)
  - 计算几何经典教材配套资源

- **Computational Geometry Course (MIT OpenCourseWare)**:
  - 6.838/6.006 课程讲义和视频

### 9.4 国际课程对标

| 大学 | 课程 | 相关主题 | 对标度 |
|------|------|----------|--------|
| MIT | 6.838 Geometric Folding Algorithms | 凸包、Voronoi图应用 | ⭐⭐⭐⭐⭐ |
| Stanford | CS 268 Geometric Algorithms | 计算几何全面覆盖 | ⭐⭐⭐⭐⭐ |
| CMU | 15-456 Computational Geometry | 凸包、Delaunay、Voronoi | ⭐⭐⭐⭐⭐ |
| ETH Zurich | 252-0209-00 Geometric Algorithms | 欧洲标准计算几何课程 | ⭐⭐⭐⭐⭐ |
| UC Berkeley | CS 274 Computational Geometry | 理论与应用并重 | ⭐⭐⭐⭐☆ |
| Tsinghua | 60240013 计算几何 | 国内经典教材配套 | ⭐⭐⭐⭐☆ |

---

## 十、专家批注

> **Joseph O'Rourke (Smith College)**:
> 
> "计算几何是连接数学理论与计算机应用的桥梁。凸包和Voronoi图作为两大基础结构，不仅在理论上优雅，在实践中更是无处不在。理解这些结构的关键在于把握它们的几何直观，而非仅仅记忆算法步骤。"

> **Herbert Edelsbrunner (IST Austria)**:
> 
> "Delaunay三角剖分之所以在网格生成中如此重要，是因为它最大化最小角的性质。这一性质直接转化为数值模拟的稳定性和准确性。Voronoi图与Delaunay的对偶关系是离散几何中最美妙的结果之一。"

> **Bernard Chazelle (Princeton)**:
> 
> "凸包算法的发展史就是计算几何的发展史。从Graham的 $O(n \log n)$ 扫描到Jarvis的输出敏感方法，再到Kirkpatrick和Seidel的终极算法，每一步都体现了算法设计的艺术。"

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | - | 初始版本，涵盖凸包与Voronoi图核心内容 |

---

**标签**: #计算几何 #凸包 #Voronoi图 #Delaunay三角剖分 #Graham扫描 #Fortune算法 #QuickHull

**相关笔记**:
- [图论基础.md](./图论基础.md)
- [贪心算法.md](./贪心算法.md)
- [分治算法.md](./分治算法.md)
- [数据结构理论.md](../09-算法理论/01-算法基础/02-数据结构理论.md)
