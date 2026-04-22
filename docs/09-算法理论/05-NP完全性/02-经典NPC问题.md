# 经典NP完全问题

## 概述

NP完全问题是一类在计算复杂性理论中具有核心地位的问题：它们满足两个条件：

1. 属于 NP（可在多项式时间内验证解）
2. 所有 NP 问题均可多项式归约到它

Cook-Levin 定理（1971）证明了**布尔可满足性问题（SAT）**是第一个 NP 完全问题。此后，通过多项式归约，数千个问题被证明为 NP 完全。

## 六大经典NP完全问题

### 1. 布尔可满足性（SAT）

**输入**：布尔公式 $\phi$（合取范式 CNF）
**问题**：是否存在变量赋值使 $\phi = \text{true}$？

**历史意义**：Cook-Levin 定理的基石，第一个被证明为 NP 完全的问题。

**特殊情形**：

- **3-SAT**：每个子句恰好 3 个文字，仍为 NP 完全
- **2-SAT**：每个子句 2 个文字，属于 P（可用强连通分量在 $O(n)$ 内解决）

### 2. 顶点覆盖（Vertex Cover）

**输入**：无向图 $G=(V,E)$，整数 $k$
**问题**：是否存在大小不超过 $k$ 的顶点子集 $C$，使得每条边至少有一个端点在 $C$ 中？

**归约路径**：3-SAT $\leq_p$ Vertex Cover

### 3. 团问题（Clique）

**输入**：无向图 $G=(V,E)$，整数 $k$
**问题**：$G$ 中是否存在大小为 $k$ 的完全子图？

**性质**：Clique 与 Independent Set、Vertex Cover 互为补图关系。

### 4. 独立集（Independent Set）

**输入**：无向图 $G=(V,E)$，整数 $k$
**问题**：是否存在 $k$ 个顶点，它们之间没有任何边？

**关系**：$S$ 是独立集 $\iff$ $V \setminus S$ 是顶点覆盖

### 5. 哈密顿回路（Hamiltonian Cycle）

**输入**：无向图 $G=(V,E)$
**问题**：是否存在经过每个顶点恰好一次的回路？

**有向版本**同样为 NP 完全。与欧拉回路（$O(E)$ 可解）形成鲜明对比。

### 6. 子集和（Subset Sum）

**输入**：整数集合 $S = \{a_1, ..., a_n\}$，目标 $t$
**问题**：是否存在子集其和恰好为 $t$？

**伪多项式算法**：动态规划 $O(n \cdot t)$，当 $t$ 为输入数值时非多项式。

## 归约关系图

```
SAT / 3-SAT
    ├──→ Vertex Cover
    │       ├──→ Independent Set
    │       └──→ Clique
    ├──→ Hamiltonian Cycle
    │       └──→ TSP（旅行商问题）
    └──→ Subset Sum
            └──→ Partition
            └──→ Knapsack
```

## 应对策略

| 策略 | 适用场景 |
|------|---------|
| 精确算法 | 小规模输入、参数化算法 |
| 近似算法 | 需要保证解的质量（如 Vertex Cover 2-近似）|
| 启发式算法 | 大规模实际应用（遗传算法、模拟退火）|
| 整数规划 | 商业求解器（Gurobi、CPLEX）|

## 代码参考

- TypeScript: `examples/algorithms-ts/src/advanced.ts` → `DancingLinks`（可用于精确覆盖 / SAT 求解）
- Rust: `examples/algorithms/src/sat2.rs`（2-SAT 专用）
