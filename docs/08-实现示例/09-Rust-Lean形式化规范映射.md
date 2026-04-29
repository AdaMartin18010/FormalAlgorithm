---
title: 09 Rust Lean形式化规范映射
concepts: ["Rust", "Lean4", "Haskell", "形式化验证", "程序提取"]
level: 中级
last_updated: 2026-04-21
---

# Rust ↔ Lean 形式化规范映射


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

本文档汇总 `examples/algorithms/`（Rust 实现）与 `examples/lean_proofs/`（Lean 4 形式化证明）之间的规范对应关系，记录已证明性质、待证义务（Proof Obligation）以及扩展路径。

---

## 一、映射总表

| 算法领域 | Rust 模块 | Lean 文件 | 已证明性质 | 待证义务 (PO) |
|---------|-----------|-----------|-----------|--------------|
| 排序-计数排序 | `counting_sort` | `counting_sort.lean` | 有序性、元素计数守恒 | PO-001: 排列性质 |
| 排序-归并排序 | `merge_sort` | `sorting_proofs.lean` | 有序性 (`mergeSort_sorted`) | 排列性质 (待扩展) |
| 图-BFS | `graph_bfs_dfs::bfs` | `graph_proofs.lean` | — | PO-003: 访问必可达; PO-004: 可达必访问 |
| 图-最短路径 | `floyd_warshall` | `floyd_warshall.lean` | 循环不变式定义 | PO-002: 算法正确性 |
| 列表基础 | — | `ListReverse.lean` | 反转对合性、append 分配律 | — |
| 自然数归纳 | — | `NatInduction.lean` | 基本算术性质 | — |

> **图例**: ✅ 已证明 (标准库可完成) | ⚠️ 待证 (需 mathlib4 或 well-founded 工具) | — 未覆盖

---

## 二、Proof Obligation 详情

### PO-001: 计数排序排列性质

- **位置**: `examples/lean_proofs/counting_sort.lean` — `binary_counting_sort_permutation`
- **陈述**: 对于仅含 0/1 的输入列表，`binaryCountingSort xs` 与 `xs` 互为排列（multiset 等价）。
- **证明思路**:
  1. 已证 `countValue (binaryCountingSort xs) 0 = countValue xs 0` 和 `countValue (binaryCountingSort xs) 1 = countValue xs 1`。
  2. 二进制输入下，上述两条即说明两个列表中 0 和 1 的数量完全相同。
  3. 由 `List.Perm` 判定定理：若两个列表中每个元素出现次数相同，则它们互为排列。
- **依赖外部工具**: mathlib4 的 `List.Perm` 定义与判定定理。
- **Rust 对应**: `counting_sort` 函数的输出与输入包含相同元素（由计数阶段的累加逻辑保证）。

### PO-002: Floyd-Warshall 算法正确性

- **位置**: `examples/lean_proofs/floyd_warshall.lean` — `floyd_warshall_correctness`
- **陈述**: 若图中不存在负权环，则算法终止后 `dist[i][j]` 等于从 `i` 到 `j` 的最短路径权重。
- **证明思路**:
  1. 对 `k` 进行数学归纳，证明循环不变式 `LoopInvariant k d n`。
  2. 基例 `k=0`：不允许任何中间顶点，距离矩阵仅含直接边权重。
  3. 归纳步骤：新最短路径 = min(旧最短路径, 经过 `k` 的最短路径)。经过 `k` 的路径可拆分为 `i→k` 与 `k→j`，两段均只使用 `{0,…,k-1}` 作为中间顶点，其最优权重已由归纳假设给出。
  4. 终止时 `k=n`，允许所有顶点作为中间点，故矩阵存储全局最短路径。
- **依赖外部工具**: mathlib4 的 `infimum` / `sInf`（定义 `shortestPathWeight`）；`WellFounded` 或 `Set.Finite`（路径集合的极小元存在性）。
- **Rust 对应**: `floyd_warshall` 函数的 `dist` 矩阵输出。

### PO-003: BFS 访问的节点都是可达的

- **位置**: `examples/lean_proofs/graph_proofs.lean` — `bfs_visits_only_reachable`
- **陈述**: BFS 访问的每个节点都是从起点可达的。
- **证明思路**:
  1. 将 `bfs_aux` 从 `partial def` 重构为 well-founded 递归（度量：未访问节点数）。
  2. 对递归结构进行归纳，维护不变式：`queue` 和 `visited` 中所有节点都可达；新加入的邻居由 `Reachable.step` 可知也可达。
- **依赖外部工具**: mathlib4 的 `Finset` / `Set.Finite`；`WellFounded` 引理。
- **Rust 对应**: `graph_bfs_dfs::bfs` 返回的 `GraphTraversalResult.visited`。

### PO-004: BFS 完备性（有限图）

- **位置**: `examples/lean_proofs/graph_proofs.lean` — `bfs_visits_all_reachable_finite`
- **陈述**: 若图是有限的且节点从起点可达，则 BFS 会将其标记为已访问。
- **证明思路**:
  1. 利用有限性假设获取所有可达节点的有限列表。
  2. 对最短路径长度进行归纳：距离为 `d` 的节点必在处理距离为 `d-1` 的节点时被加入队列。
- **依赖外部工具**: `Finset` / `Set.Finite`；`Nat.measure` 或 `WellFounded`。
- **Rust 对应**: `graph_bfs_dfs::bfs` 在有限图上的完备性。

---

## 三、规范模板（供未来扩展）

为新增算法建立 Rust ↔ Lean 映射时，请遵循以下模板：

### 3.1 Rust 源码注释模板

在 Rust 模块文档注释（`//!`）或函数文档注释（`///`）末尾添加：

```rust
//! ## 形式化规范 (Formal Specification)
//!
//! 对应 Lean 证明: [`examples/lean_proofs/<file>.lean`]
//!
//! | Rust 规范 | Lean 谓词/定理 | 状态 |
//! |-----------|---------------|------|
//! | <规范描述> | `<lean_definition>` | ✅/⚠️/— |
```

### 3.2 Lean 文件模板

新建 Lean 证明文件时，请在顶部添加：

```lean
/-
  <algorithm>.lean
  <算法>正确性的形式化证明（Lean 4）

  对应 Rust 实现: examples/algorithms/src/<module>.rs

  证明目标：
  1. <性质 1>
  2. <性质 2>

  状态：
  - ✅ <已证定理>
  - ⚠️ <待证义务> (PO-XXX)
-/
```

### 3.3 新增 Proof Obligation 编号规则

- 格式：`PO-NNN`
- 分配：按创建顺序递增，从 PO-005 开始
- 记录位置：本文件第 二 节 + 对应 Lean 文件的 `sorry` 旁注释

---

## 四、环境限制与解锁条件

当前 Lean 环境无法从 GitHub 下载 mathlib4（`lean` / `lake` 命令触发网络超时），因此所有依赖 mathlib4 的 Proof Obligation 暂时无法推进。

**解锁条件**：

1. 配置 Lean 依赖镜像（如清华 tuna 镜像、Azure CDN 镜像）
2. 或本地预编译 mathlib4 缓存
3. 或等待网络环境恢复后执行 `lake update` 和 `lake build`

解锁后建议优先顺序：

1. PO-001（`List.Perm` 工具相对轻量）
2. PO-003 / PO-004（BFS 性质，图论基础）
3. PO-002（Floyd-Warshall，涉及 infimum 和路径权重，复杂度最高）

---

## 五、相关文档

- [`03-Lean实现.md`](./03-Lean实现.md) — Lean 4 语言特性与项目实现说明
- [`04-形式化验证.md`](./04-形式化验证.md) — 形式化验证方法论与工具链
- `examples/lean_proofs/README.md` — Lean 证明库目录说明（待创建）

---

## 参考文献

- [CLRS2009] T. H. Cormen et al. Introduction to Algorithms (3rd ed.). MIT Press, 2009.
- [Sipser2012] M. Sipser. Introduction to the Theory of Computation (3rd ed.). Cengage Learning, 2012.
- [Pierce2002] B. C. Pierce. Types and Programming Languages. MIT Press, 2002.

---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解Rust ↔ Lean 形式化规范映射的核心概念
- 掌握Rust ↔ Lean 形式化规范映射的形式化表示
