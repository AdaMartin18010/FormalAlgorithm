#!/usr/bin/env python3
# -*- coding: utf-8 -*-
"""
LeetCode算法面试专题 - 严重缺失文档修复脚本
"""

import os
import re

BASE_DIR = r"e:\_src\FormalAlgorithm\docs\13-LeetCode算法面试专题"

def read_file(path):
    with open(path, 'r', encoding='utf-8') as f:
        return f.read()

def write_file(path, content):
    with open(path, 'w', encoding='utf-8') as f:
        f.write(content)

# ===================== 修复 01-高频Top100-数组与链表.md =====================
def fix_01_array_linkedlist(content):
    # 查找插入点：在 "## 1. 范式一：前缀和" 之前插入形式化定义与定理章节
    insert_marker = "## 1. 范式一：前缀和"
    
    new_section = """## 0. 形式化定义与核心定理

在深入具体题目之前，我们先建立数组与链表操作的形式化基础，并给出贯穿本章的核心定理及其证明。

### 0.1 形式化定义

> **定义 1.1**（数组 / Array）
> 数组是有限个同类型元素构成的有序序列，形式化表示为 $A = (a_0, a_1, \ldots, a_{n-1})$，其中 $n \in \mathbb{N}$ 为数组长度，$a_i \in \mathcal{T}$ 为第 $i$ 个元素，$\mathcal{T}$ 为元素类型。数组支持通过下标 $i$ 在 $O(1)$ 时间内随机访问 $a_i$。

> **定义 1.2**（链表 / Linked List）
> 链表是由节点通过指针链接而成的线性数据结构。每个节点 $v$ 包含数据域 $v.\text{data}$ 和指针域 $v.\text{next}$。形式化地，链表 $L$ 可递归定义为：
> - 空链表 $L = \text{nil}$
> - 非空链表 $L = v \to L'$，其中 $v$ 为头节点，$L'$ 为剩余链表

> **定义 1.3**（原地算法 / In-Place Algorithm）
> 称算法为原地的，当且仅当其除输入输出外使用的额外空间为 $O(1)$，即空间复杂度 $S(n) = O(1)$。

> **定义 1.4**（双指针 / Two Pointers）
> 双指针技术使用两个索引 $i, j$（或指针 $p, q$）协同遍历数据结构。根据移动策略分为：
> - **对撞指针**：$i$ 从头部向右，$j$ 从尾部向左，相向移动
> - **快慢指针**：$i$ 和 $j$ 同向移动，但步长不同（如 $i$ 每次1步，$j$ 每次2步）

### 0.2 核心定理与证明

> **定理 1.1**（对撞双指针覆盖定理）
> 设有序数组 $A[0..n-1]$，对撞双指针从 $l=0, r=n-1$ 开始相向移动。若移动策略保证"每次至少排除一个不可能包含解的元素"，则算法不会遗漏任何有效解。

**证明**：

我们使用循环不变式证明。

**循环不变式** $I$：
$$
I(l, r) \equiv \text{若解存在，则解的所有元素均位于 } [l, r] \text{ 区间内}
$$

**初始化**：$l=0, r=n-1$。显然若解存在，其元素必在 $[0, n-1]$ 中，$I$ 成立。

**保持**：假设某次迭代前 $I$ 成立。根据具体问题的排除规则（如 $A[l] + A[r]$ 与目标值比较），我们排除 $A[l]$ 或 $A[r]$ 中至少一个不可能属于解的元素，将 $l$ 右移或 $r$ 左移。由于被排除的元素经论证确实不可能属于任何解，$I$ 对新区间仍成立。

**终止**：当 $l \geq r$ 时循环终止。此时区间内至多一个元素，若解存在则必为该元素。证毕。$\square$

> **定理 1.2**（滑动窗口不变式定理）
> 对于子数组/子串搜索问题，设滑动窗口为 $[left, right]$，若不变式 $Inv(right) \equiv$"窗口 $[left, right)$ 始终满足某性质 $P$" 在每次 $right$ 扩展后通过调整 $left$ 得以保持，则算法返回的极大（或极小）窗口即为全局最优解。

**证明**：

对 $right$ 的遍历进行归纳。

**基础**：$right = 0$，窗口为空，性质 $P$ 平凡成立。

**归纳假设**：设 $right = k$ 时，存在某个 $left$ 使得 $[left, k)$ 满足 $P$，且所有以 $k$ 结尾的满足 $P$ 的窗口中，$[left, k)$ 是最靠左的（即 $left$ 最小）。

**归纳步**：$right$ 扩展到 $k+1$。若 $[left, k+1)$ 仍满足 $P$，则不变式保持。否则，将 $left$ 右移至最小的 $left' > left$ 使得 $[left', k+1)$ 满足 $P$。由构造可知，$[left', k+1)$ 是以 $k+1$ 结尾的最小左边界窗口。若不存在这样的 $left'$，则窗口为空（$left = k+1$），性质 $P$ 仍平凡成立。

因此，每次 $right$ 扩展后，我们维护了以当前 $right$ 结尾的最优窗口。遍历结束后，所有右边界对应的最优窗口中的极值即为全局最优。证毕。$\square$

> **定理 1.3**（Floyd 判圈定理）
> 设链表存在环，环长为 $C$。慢指针每次移动1步，快指针每次移动2步，则两指针必在有限步内相遇。

**证明**：

设慢指针进入环时，快指针已在环内领先 $d$ 步（$0 \leq d < C$）。此后每步快指针追近 $1$ 步（相对速度为 $2-1=1$）。经过 $C - d$ 步后，快指针恰好追上慢指针。因 $C - d \leq C < \infty$，相遇在有限步内发生。证毕。$\square$

### 0.3 思维表征

```mermaid
graph TD
    A[数组与链表高频题] --> B[前缀和]
    A --> C[双指针]
    A --> D[滑动窗口]
    A --> E[链表操作]
    A --> F[矩阵]
    A --> G[区间]
    A --> H[排序]
    C --> C1[对撞指针]
    C --> C2[快慢指针]
    E --> E1[三指针反转]
    E --> E2[哨兵节点]
```

```mermaid
flowchart TD
    Start[面试遇到数组/链表题] --> Q1{是否需要查找配对?}
    Q1 -->|是| Q2{数组是否有序?}
    Q1 -->|否| Q3{是否需要维护子数组?}
    Q2 -->|是| A1[对撞双指针]
    Q2 -->|否| A2[哈希表/前缀和]
    Q3 -->|是| A3[滑动窗口]
    Q3 -->|否| Q4{数据结构?}
    Q4 -->|链表| A4[三指针/快慢指针]
    Q4 -->|矩阵| A5[转置/边界收缩]
```

```mermaid
graph LR
    Def1[定义1.1 数组] --> Thm1[定理1.1 对撞指针]
    Def2[定义1.2 链表] --> Thm2[定理1.3 Floyd判圈]
    Def3[定义1.4 双指针] --> Thm1
    Def4[定义1.3 原地算法] --> App1[应用: 原地旋转]
    Thm1 --> Proof[循环不变式证明]
    Thm2 --> Proof2[模运算追及证明]
```

---

"""
    
    if insert_marker in content:
        content = content.replace(insert_marker, new_section + insert_marker, 1)
    
    # 添加学习目标（在参考文献之前）
    lo_section = """## 11. 学习目标

完成本章学习后，读者应能够：

1. **形式化描述**数组和链表的基本操作及其复杂度下界。
2. **熟练运用**双指针、滑动窗口、前缀和三大范式解决高频面试题。
3. **独立推导**基于循环不变式的正确性证明（初始化、保持、终止三条件）。
4. **快速识别**题目适用的算法范式，并口述解题思路与复杂度分析。
5. **系统处理**链表边界情况（空链表、单节点、头节点删除）。

---

"""
    
    ref_marker = "## 参考文献"
    if ref_marker in content and "## 11. 学习目标" not in content:
        content = content.replace(ref_marker, lo_section + ref_marker, 1)
    
    return content

# ===================== 修复 02-高频Top100-树与图.md =====================
def fix_02_tree_graph(content):
    insert_marker = "## 1. 范式一：树的遍历"
    
    new_section = """## 0. 形式化定义与核心定理

### 0.1 形式化定义

> **定义 2.1**（二叉树 / Binary Tree）
> 二叉树 $T$ 要么为空（$T = \text{nil}$），要么由一个根节点 $r$ 和两棵不相交的二叉树 $T_L, T_R$ 组成，记作 $T = (r, T_L, T_R)$。节点数记为 $|T|$，高度记为 $h(T) = 1 + \max(h(T_L), h(T_R))$（空树高度为0）。

> **定义 2.2**（二叉搜索树 / BST）
> 二叉搜索树是满足以下条件的二叉树：对任意节点 $v$，其左子树中所有节点值小于 $v.\text{val}$，右子树中所有节点值大于 $v.\text{val}$。形式化地：
> $$
> \forall x \in T_L: x.\text{val} < v.\text{val} \quad \land \quad \forall y \in T_R: y.\text{val} > v.\text{val}
> $$

> **定义 2.3**（图 / Graph）
> 图 $G = (V, E)$ 由顶点集 $V$ 和边集 $E \subseteq V \times V$ 组成。若边无方向，称 $G$ 为无向图；若有方向，称有向图。边权函数 $w: E \to \mathbb{R}$ 给每条边赋权。

> **定义 2.4**（最近公共祖先 / LCA）
> 设二叉树 $T$ 中节点 $p, q$ 均存在。节点 $r$ 称为 $p$ 和 $q$ 的最近公共祖先，当且仅当：
> 1. $r$ 是 $p$ 和 $q$ 的公共祖先（$p, q$ 均在以 $r$ 为根的子树中）
> 2. $r$ 的深度最大（即不存在 $r$ 的子孙也是 $p, q$ 的公共祖先）

### 0.2 核心定理与证明

> **定理 2.1**（BST 中序遍历有序性定理）
> 对任意二叉搜索树 $T$，其中序遍历（左-根-右）输出的序列严格递增。

**证明**：

对树的结构进行归纳（结构归纳法）。

**基础**：$|T| = 0$（空树），中序遍历输出空序列，平凡有序。

**归纳假设**：设 $|T| < n$ 时定理成立。

**归纳步**：考虑 $|T| = n$ 的 BST，根为 $r$，左子树 $T_L$，右子树 $T_R$。由 BST 定义，$\forall x \in T_L: x < r$ 且 $\forall y \in T_R: y > r$。中序遍历输出为 $InOrder(T_L) \oplus [r] \oplus InOrder(T_R)$。由归纳假设，$InOrder(T_L)$ 和 $InOrder(T_R)$ 分别有序；又由 BST 性质，$InOrder(T_L)$ 中所有元素 $< r <$ $InOrder(T_R)$ 中所有元素。因此整体序列有序。证毕。$\square$

> **定理 2.2**（Dijkstra 最优性子定理）
> 在边权均为非负的带权图 $G = (V, E, w)$ 中，设 $S$ 为已确定最短距离的顶点集合。每次从 $V \setminus S$ 中选择距离估计值最小的顶点 $u$ 加入 $S$ 时，$d[u]$ 即为源点 $s$ 到 $u$ 的最短距离。

**证明**：

采用反证法。设 $u$ 是被选中的顶点，假设存在一条更短的路径 $P$ 从 $s$ 到 $u$，其长度 $< d[u]$。由于 $s \in S$ 而 $u \notin S$，路径 $P$ 必经过某条从 $S$ 到 $V \setminus S$ 的边。设 $P$ 上第一个属于 $V \setminus S$ 的顶点为 $x$，则 $P$ 可分解为 $s \leadsto y \to x \leadsto u$，其中 $y \in S$。由于所有边权非负，$len(s \leadsto x) \leq len(P) < d[u]$。但 $d[x]$ 作为 $x$ 的距离估计值，满足 $d[x] \leq len(s \leadsto x) < d[u]$，这与 $u$ 是 $V \setminus S$ 中距离估计值最小的顶点矛盾。因此 $d[u]$ 已是最短距离。证毕。$\square$

> **定理 2.3**（树形 DP 最优子结构定理）
> 设树形 DP 的状态 $dp[v]$ 表示以 $v$ 为根的子树上的最优值。若状态转移方程满足：
> $$
> dp[v] = f(v.\text{val}, dp[v_L], dp[v_R])
> $$
> 其中 $f$ 为某种合并函数，则 $dp[v]$ 可由子树最优值正确计算。

**证明**：

对树高进行归纳。

**基础**：$h = 0$（叶子节点），$dp[v] = f(v.\text{val}, \text{nil}, \text{nil})$，正确。

**归纳假设**：设对所有高度 $< h$ 的子树，DP 值正确。

**归纳步**：对高度为 $h$ 的节点 $v$，其左右子树高度均 $< h$。由归纳假设，$dp[v_L]$ 和 $dp[v_R]$ 分别为左右子树的最优值。若问题的最优解包含子问题的最优解（最优子结构），则 $dp[v] = f(v.\text{val}, dp[v_L], dp[v_R])$ 必为以 $v$ 为根的子树的最优值。证毕。$\square$

### 0.3 思维表征

```mermaid
graph TD
    A[树与图高频题] --> B[树的遍历]
    A --> C[LCA与树形DP]
    A --> D[序列化]
    A --> E[图搜索]
    A --> F[最短路径]
    A --> G[拓扑排序]
    A --> H[MST与并查集]
    B --> B1[前序/中序/后序]
    B --> B2[BFS层序]
    E --> E1[DFS]
    E --> E2[BFS]
```

```mermaid
flowchart TD
    Start[面试遇到树/图题] --> Q1{数据结构类型?}
    Q1 -->|树| Q2{需要找祖先?}
    Q1 -->|图| Q3{边有权?}
    Q2 -->|是| A1[LCA算法]
    Q2 -->|否| Q4{需要最优值?}
    Q4 -->|是| A2[树形DP]
    Q4 -->|否| A3[遍历/序列化]
    Q3 -->|是| A4[Dijkstra/Bellman-Ford]
    Q3 -->|否| Q5{需要判环?}
    Q5 -->|是| A5[拓扑排序/DFS染色]
    Q5 -->|否| A6[DFS/BFS/并查集]
```

```mermaid
graph LR
    Def1[定义2.1 二叉树] --> Thm1[定理2.1 BST中序有序]
    Def2[定义2.3 图] --> Thm2[定理2.2 Dijkstra最优性]
    Def3[定义2.4 LCA] --> App1[应用: 二叉树LCA]
    Thm1 --> Proof[结构归纳法证明]
    Thm2 --> Proof2[反证法证明]
```

---

"""
    
    if insert_marker in content:
        content = content.replace(insert_marker, new_section + insert_marker, 1)
    
    # 添加学习目标
    lo_section = """## 11. 学习目标

完成本章学习后，读者应能够：

1. **形式化描述**二叉树、BST、图、LCA 等核心概念。
2. **熟练运用**树遍历（前序/中序/后序/层序）和图搜索（DFS/BFS）解决高频题。
3. **独立推导**Dijkstra 最优性证明和树形 DP 最优子结构证明。
4. **快速识别**LCA、树形 DP、拓扑排序、MST 等问题的适用场景。
5. **在面试中**用结构归纳法证明树相关算法的正确性。

---

"""
    
    ref_marker = "## 参考文献"
    if ref_marker in content and "## 11. 学习目标" not in content:
        content = content.replace(ref_marker, lo_section + ref_marker, 1)
    
    return content

# ===================== 修复 03-高频Top100-DP与贪心.md =====================
def fix_03_dp_greedy(content):
    insert_marker = "## 1. 范式一：线性DP"
    
    new_section = """## 0. 形式化定义与核心定理

### 0.1 形式化定义

> **定义 3.1**（最优子结构 / Optimal Substructure）
> 问题 $\mathcal{P}$ 具有最优子结构，当且仅当其任意最优解 $OPT$ 所包含的子问题的解 $OPT'$ 也是对应子问题的最优解。形式化地：
> $$
> \text{OPT}(\mathcal{P}) = \text{combine}\big(v, \text{OPT}(\mathcal{P}_1), \text{OPT}(\mathcal{P}_2), \ldots, \text{OPT}(\mathcal{P}_k)\big)
> $$
> 其中 $\mathcal{P}_i$ 为 $\mathcal{P}$ 的子问题，$v$ 为当前决策的代价/收益。

> **定义 3.2**（重叠子问题 / Overlapping Subproblems）
> 问题 $\mathcal{P}$ 具有重叠子问题性质，当且仅当在递归求解过程中，同一子问题被多次求解。即递归调用树中不同路径上存在相同的子问题实例。

> **定义 3.3**（贪心选择性质 / Greedy Choice Property）
> 问题 $\mathcal{P}$ 具有贪心选择性质，当且仅当存在一个局部最优选择（贪心选择），将其包含在全局最优解中后，剩余的子问题仍然可以被最优求解。形式化地，存在贪心选择 $g$ 使得：
> $$
> \exists g: \text{OPT} = \{g\} \cup \text{OPT}(\mathcal{P}')
> $$
> 其中 $\mathcal{P}'$ 为做出选择 $g$ 后的子问题。

> **定义 3.4**（状态与状态转移方程）
> DP 状态 $dp[s]$ 是描述子问题特征的变量集合的函数。状态转移方程定义了从已知状态推导新状态的递推关系：
> $$
> dp[s] = \text{transition}\big(dp[s_1], dp[s_2], \ldots, dp[s_m], \text{input}\big)
> $$

### 0.2 核心定理与证明

> **定理 3.1**（DP 最优子结构传递定理）
> 若问题 $\mathcal{P}$ 具有最优子结构，且状态转移方程 $dp[s] = f(dp[s_1], \ldots)$ 中的 $f$ 对最优解具有保优性（即子问题最优 $\Rightarrow$ 父问题最优），则通过自底向上计算 $dp$ 表得到的 $dp[s_0]$（$s_0$ 为初始状态）是原问题的最优值。

**证明**：

对状态依赖图进行拓扑序归纳。

**基础**：所有无依赖的状态（边界状态）直接初始化，其最优性由问题定义保证。

**归纳假设**：设所有在拓扑序中位于状态 $s$ 之前的状态均已计算出最优值。

**归纳步**：状态 $s$ 依赖 $s_1, \ldots, s_m$。由归纳假设，$dp[s_i]$ 均为子问题最优值。由最优子结构，$s$ 的最优解必由某个（或某些）$s_i$ 的最优解组合而成。状态转移方程 $f$ 遍历了所有可能的组合方式并取最优，因此 $dp[s]$ 必为 $s$ 对应子问题的最优值。

由归纳法，所有状态（包括 $s_0$）均得到最优值。证毕。$\square$

> **定理 3.2**（贪心选择正确性定理 — 交换论证框架）
> 设问题 $\mathcal{P}$ 具有贪心选择性质，$g$ 为贪心算法的第一步选择。若对任意最优解 $OPT$ 都可以将其第一步替换为 $g$ 而得到另一个不更差的最优解 $OPT'$，则贪心算法最优。

**证明**：

设贪心算法的选择序列为 $G = (g_1, g_2, \ldots, g_k)$，$OPT$ 为任意最优解。

**第一步替换**：由条件，可将 $OPT$ 的第一步替换为 $g_1$ 得到 $OPT_1$，满足 $|OPT_1| = |OPT|$ 且 $OPT_1$ 可行。

**迭代替换**：对 $OPT_1$ 的剩余子问题重复上述替换，将 $g_2$ 代入得到 $OPT_2$，依此类推。

**终止**：经过 $k$ 步替换后，得到 $OPT_k = G$。由于每次替换都不降低解的质量，$G$ 与 $OPT$ 同样最优。

因此贪心算法 $G$ 是最优的。证毕。$\square$

> **定理 3.3**（区间 DP 正确性定理）
> 对于区间 $[i, j]$ 上的最优值 $dp[i][j]$，若状态转移枚举了所有合法的分割点 $k \in (i, j)$ 并取最优，且计算顺序按区间长度从小到大，则 $dp[i][j]$ 正确。

**证明**：

对区间长度 $len = j - i$ 进行归纳。

**基础**：$len = 0$ 或 $1$（相邻或空区间），边界条件正确。

**归纳假设**：设所有长度 $< len$ 的区间已正确计算。

**归纳步**：对长度 $len$ 的区间 $[i, j]$，转移枚举 $k \in (i, j)$。每个子区间 $[i, k]$ 和 $[k, j]$ 的长度均 $< len$，由归纳假设其 $dp$ 值正确。转移取遍所有 $k$ 的最优组合，因此 $dp[i][j]$ 正确。证毕。$\square$

### 0.3 思维表征

```mermaid
graph TD
    A[DP与贪心高频题] --> B[线性DP]
    A --> C[区间DP]
    A --> D[树形DP]
    A --> E[状态压缩DP]
    A --> F[背包问题]
    A --> G[贪心]
    B --> B1[LIS/打家劫舍]
    C --> C1[回文/戳气球]
    G --> G1[交换论证]
    G --> G2[区间调度]
```

```mermaid
flowchart TD
    Start[面试遇到优化问题] --> Q1{是否具有最优子结构?}
    Q1 -->|否| A1[无法DP/贪心]
    Q1 -->|是| Q2{是否具有贪心选择性质?}
    Q2 -->|是| Q3{能否快速验证?}
    Q2 -->|否| A2[动态规划]
    Q3 -->|是| A3[贪心算法]
    Q3 -->|否| A2
    A2 --> Q4{状态维度?}
    Q4 -->|一维顺序| A4[线性DP]
    Q4 -->|区间| A5[区间DP]
    Q4 -->|树| A6[树形DP]
    Q4 -->|集合| A7[状态压缩DP]
```

```mermaid
graph LR
    Def1[定义3.1 最优子结构] --> Thm1[定理3.1 DP最优性]
    Def2[定义3.3 贪心选择] --> Thm2[定理3.2 贪心正确性]
    Def3[定义3.4 状态转移] --> Thm3[定理3.3 区间DP正确性]
    Thm1 --> Proof1[拓扑序归纳]
    Thm2 --> Proof2[交换论证]
    Thm3 --> Proof3[区间长度归纳]
```

---

"""
    
    if insert_marker in content:
        content = content.replace(insert_marker, new_section + insert_marker, 1)
    
    # 添加学习目标
    lo_section = """## 10. 学习目标

完成本章学习后，读者应能够：

1. **严格区分**动态规划与贪心算法的适用条件（最优子结构 vs 贪心选择性质）。
2. **熟练运用**交换论证证明贪心算法的正确性。
3. **独立设计**线性 DP、区间 DP、树形 DP、状态压缩 DP 的状态与转移方程。
4. **掌握**背包问题的多种变形及其转化技巧（0/1背包、完全背包、多重背包）。
5. **在面试中**用归纳法证明 DP 状态的最优性。

---

"""
    
    ref_marker = "## 参考文献"
    if ref_marker in content and "## 10. 学习目标" not in content:
        content = content.replace(ref_marker, lo_section + ref_marker, 1)
    
    return content

# ===================== 修复 04-剑指Offer精选形式化证明.md =====================
def fix_04_jianzhioffer(content):
    # 在 "## 1. 形式化方法导论" 之前添加形式化定义章节
    insert_marker = "## 1. 形式化方法导论"
    
    new_section = """## 0. 形式化基础定义

> **定义 4.1**（问题五元组 / Problem Quintuple）
> 算法问题的形式化规约由五元组 $\Pi = (D, I, O, \text{pre}, \text{post})$ 组成：
> - $D$：数据域（data domain），描述输入数据的类型与结构
> - $I \subseteq D$：输入集合（input set），满足前置条件的有效输入
> - $O$：输出集合（output set），描述输出数据的类型
> - $\text{pre}: D \to \{\text{true}, \text{false}\}$：前置条件，算法可假设的输入约束
> - $\text{post}: D \times O \to \{\text{true}, \text{false}\}$：后置条件，算法必须保证的输出性质

> **定义 4.2**（循环不变式 / Loop Invariant）
> 设循环的迭代变量为 $i$，谓词 $Inv(i)$ 称为循环不变式，当且仅当满足以下三条件：
> 1. **初始化**：$Inv(i_0)$ 在循环开始前成立
> 2. **保持**：若 $Inv(i)$ 在某次迭代前成立，则执行循环体后 $Inv(i+1)$ 仍成立
> 3. **终止**：当循环终止时，$Inv(i_{\text{end}})$ 蕴含后置条件 $\text{post}$

> **定义 4.3**（结构归纳法 / Structural Induction）
> 结构归纳法是数学归纳法在递归数据结构上的推广。对二叉树的结构归纳包含：
> 1. **基础**：命题对空树（和/或单节点树）成立
> 2. **归纳**：假设命题对左子树 $T_L$ 和右子树 $T_R$ 成立，证明对整棵树 $T = (r, T_L, T_R)$ 成立

### 0.1 核心定理

> **定理 4.1**（五元组规约完备性定理）
> 若算法 $A$ 对所有满足 $\text{pre}(x)$ 的输入 $x \in I$ 都能终止，且终止时满足 $\text{post}(x, A(x))$，则称 $A$ 关于规约 $\Pi$ 是完全正确（totally correct）的。

**证明**：由完全正确性的定义直接可得。$\text{pre}$ 保证输入合法性，$\text{post}$ 保证输出正确性，终止性由算法分析保证。证毕。$\square$

> **定理 4.2**（循环不变式蕴含正确性定理）
> 若循环不变式 $Inv$ 满足初始化、保持、终止三条件，则基于该循环的算法是正确的。

**证明**：

**初始化**保证循环开始前断言成立；**保持**保证若某次迭代前断言成立，则下一次迭代前也成立。由数学归纳法，断言在每次迭代前均成立。**终止**条件保证循环结束时断言蕴含后置条件。因此算法满足其规约。证毕。$\square$

---

"""
    
    if insert_marker in content:
        content = content.replace(insert_marker, new_section + insert_marker, 1)
    
    # 将现有的 "定理：" 替换为 "**定理 X.X**" 格式
    # 但需要智能地匹配已有的定理
    theorem_mappings = [
        ("**定理**：递归函数 `printNumbers(digit, n)` 恰好生成所有 n 位数字排列一次。", "**定理 4.3**：递归函数 `printNumbers(digit, n)` 恰好生成所有 n 位数字排列一次。"),
        ("**定理**：`reversePrint(head)` 返回以 `head` 为头的链表的逆序值数组。", "**定理 4.4**：`reversePrint(head)` 返回以 `head` 为头的链表的逆序值数组。"),
        ("**定理**：树对称当且仅当左子树和右子树互为镜像。", "**定理 4.5**：树对称当且仅当左子树和右子树互为镜像。"),
        ("**定理**：`buildTree(preorder, inorder)` 正确重建二叉树。", "**定理 4.6**：`buildTree(preorder, inorder)` 正确重建二叉树。"),
        ("**定理**：`isMatch(a, b)` 返回 true 当且仅当以 `a` 为根的子树包含 `b` 为子结构。", "**定理 4.7**：`isMatch(a, b)` 返回 true 当且仅当以 `a` 为根的子树包含 `b` 为子结构。"),
        ("**定理**：算法返回 $F(n) \bmod M$。", "**定理 4.8**：算法返回 $F(n) \bmod M$。"),
        ("**定理**：到达 $(i,j)$ 的最优路径必然经过 $(i-1,j)$ 或 $(i,j-1)$ 的最优路径。", "**定理 4.9**：到达 $(i,j)$ 的最优路径必然经过 $(i-1,j)$ 或 $(i,j-1)$ 的最优路径。"),
    ]
    
    for old, new in theorem_mappings:
        content = content.replace(old, new, 1)
    
    return content

# ===================== 修复 05-大厂真题分类.md =====================
def fix_05_bigtech(content):
    # 在 "## 1. 大厂考察总览" 之前添加形式化定义与定理
    insert_marker = "## 1. 大厂考察总览"
    
    new_section = """## 0. 形式化定义与核心定理

### 0.1 形式化定义

> **定义 5.1**（LRU 缓存 / Least Recently Used Cache）
> LRU 缓存是容量为 $C$ 的数据结构，支持两种操作：
> - $\text{get}(k)$：若键 $k$ 存在，返回其值并将其标记为最近使用；否则返回 $-1$
> - $\text{put}(k, v)$：插入/更新键值对 $(k, v)$。若缓存已满，淘汰最久未使用的键
> 形式化地，维护使用序列表 $L$，每次访问后将对应键移至 $L$ 头部；淘汰时移除 $L$ 尾部。

> **定义 5.2**（快速选择 / Quickselect）
> 快速选择是基于快速排序分区思想的第 $k$ 小元素选择算法。给定数组 $A$ 和整数 $k$，选择 pivot $p$ 将 $A$ 划分为 $A_{<p}$ 和 $A_{>p}$。若 $|A_{<p}| = k-1$，则 $p$ 为第 $k$ 小；否则递归到对应子数组。

> **定义 5.3**（中位数 / Median）
> 对于有序序列 $S = (s_1, s_2, \ldots, s_n)$，中位数定义为：
> $$
> \text{median}(S) = \begin{cases}
> s_{\lceil n/2 \rceil}, & n \text{ 为奇数} \\
> \frac{1}{2}(s_{n/2} + s_{n/2+1}), & n \text{ 为偶数}
> \end{cases}
> $$

### 0.2 核心定理与证明

> **定理 5.1**（LRU 均摊 $O(1)$ 定理）
> 使用哈希表 + 双向链表实现的 LRU 缓存，$\text{get}$ 和 $\text{put}$ 操作的均摊时间复杂度均为 $O(1)$。

**证明**：

**get 操作**：哈希表查找键到节点的映射为 $O(1)$。将节点从链表中移除并插入头部：双向链表的删除和头插均为 $O(1)$（已知节点指针）。因此单次 $\text{get}$ 最坏 $O(1)$。

**put 操作**：
- 若键已存在：更新值 + 移到头部，$O(1)$。
- 若键不存在且缓存未满：哈希表插入 $O(1)$ + 链表头插 $O(1)$。
- 若键不存在且缓存已满：哈希表删除尾部键 $O(1)$ + 链表尾删 $O(1)$ + 哈希表插入 $O(1)$ + 链表头插 $O(1)$。

因此单次 $\text{put}$ 最坏 $O(1)$，均摊亦为 $O(1)$。证毕。$\square$

> **定理 5.2**（快速选择期望线性定理）
> 在随机 pivot 选择下，快速选择算法的期望时间复杂度为 $O(n)$。

**证明**：

设 $T(n)$ 为在长度为 $n$ 的数组上的期望运行时间。随机 pivot 将数组分为大小为 $i$ 和 $n-1-i$ 的两部分（$i = 0, \ldots, n-1$，等概率）。由于只递归处理包含目标的一侧：

$$
T(n) \leq n + \frac{1}{n} \sum_{i=0}^{n-1} T(\max(i, n-1-i))
$$

注意到 $\max(i, n-1-i) \leq \lceil n/2 \rceil - 1$ 当 $i$ 取中间值时。更精确地，利用对称性：

$$
T(n) \leq n + \frac{2}{n} \sum_{i=\lfloor n/2 \rfloor}^{n-1} T(i)
$$

假设 $T(k) \leq ck$ 对所有 $k < n$ 成立，代入得：

$$
T(n) \leq n + \frac{2c}{n} \sum_{i=\lfloor n/2 \rfloor}^{n-1} i \leq n + \frac{2c}{n} \cdot \frac{3n^2}{8} = n + \frac{3cn}{4}
$$

取 $c = 4$，则 $T(n) \leq 4n = O(n)$。由归纳法，期望时间 $O(n)$。证毕。$\square$

> **定理 5.3**（中位数二分搜索下界定理）
> 在基于比较的模型中，查找两个有序数组的中位数需要 $\Omega(\log(m+n)))$ 次比较。

**证明**：

考虑决策树模型。两个有序数组的合并结果有 $\binom{m+n}{m}$ 种可能的交错方式（选择 $m$ 个位置给第一个数组）。中位数问题等价于确定合并后序列的中间元素，其信息量为 $\log_2 \binom{m+n}{m}$。由 Stirling 近似，$\binom{m+n}{m} \approx \frac{(m+n)^{m+n}}{m^m n^n}$，取对数得：

$$
\log_2 \binom{m+n}{m} \approx (m+n)H\Big(\frac{m}{m+n}\Big)
$$

其中 $H$ 为二元熵函数。特别地，当 $m = n$ 时，$\log_2 \binom{2n}{n} \approx 2n - O(\log n)$。但中位数问题不需要完全排序，只需确定中间位置。基于比较的下界为 $\Omega(\log(m+n))$，因为每次比较至多排除一半的候选中位数位置。证毕。$\square$

### 0.3 思维表征

```mermaid
graph TD
    A[大厂真题20道] --> B[字节跳动]
    A --> C[阿里巴巴]
    A --> D[腾讯]
    A --> E[Google]
    B --> B1[滑动窗口/双指针]
    B --> B2[设计题LRU]
    E --> E1[二分/分治]
    E --> E2[区间DP]
    E --> E3[严格证明]
```

```mermaid
graph LR
    Def1[定义5.1 LRU] --> Thm1[定理5.1 O(1)均摊]
    Def2[定义5.2 快速选择] --> Thm2[定理5.2 期望O(n)]
    Def3[定义5.3 中位数] --> Thm3[定理5.3 下界Ω(log n)]
    Thm1 --> Proof1[摊销分析]
    Thm2 --> Proof2[期望归纳]
    Thm3 --> Proof3[决策树/信息论]
```

---

"""
    
    if insert_marker in content:
        content = content.replace(insert_marker, new_section + insert_marker, 1)
    
    # 添加学习目标
    lo_section = """## 9. 学习目标

完成本章学习后，读者应能够：

1. **形式化描述**LRU 缓存、快速选择、中位数等高频面试概念。
2. **独立证明**LRU 均摊 $O(1)$、快速选择期望 $O(n)$ 等核心结论。
3. **针对字节/阿里/腾讯/Google** 四家公司的考察特点调整面试策略。
4. **用决策树和信息论**论证算法复杂度下界。
5. **在面试中**完成 STAR-Algorithm 标准口述结构（Situation-Trade-off-Algorithm-Reasoning-Termination）。

---

"""
    
    ref_marker = "## 参考文献"
    if ref_marker in content and "## 9. 学习目标" not in content:
        content = content.replace(ref_marker, lo_section + ref_marker, 1)
    
    return content


def main():
    fixes = [
        ("06-面试专题/01-高频Top100-数组与链表.md", fix_01_array_linkedlist),
        ("06-面试专题/02-高频Top100-树与图.md", fix_02_tree_graph),
        ("06-面试专题/03-高频Top100-DP与贪心.md", fix_03_dp_greedy),
        ("06-面试专题/04-剑指Offer精选形式化证明.md", fix_04_jianzhioffer),
        ("06-面试专题/05-大厂真题分类（字节-阿里-腾讯-Google）.md", fix_05_bigtech),
    ]
    
    for rel_path, fix_func in fixes:
        full_path = os.path.join(BASE_DIR, rel_path)
        print(f"修复: {rel_path}")
        content = read_file(full_path)
        new_content = fix_func(content)
        write_file(full_path, new_content)
        print(f"  ✓ 完成")
    
    print("\n所有修复已完成！")

if __name__ == '__main__':
    main()
