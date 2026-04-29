---
title: 示例库 · HoTT 示例 / Homotopy Type Theory Examples
version: 1.0
status: maintained
last_updated: 2026-04-20
---

> 本文档集中管理 FormalAlgorithm 项目中重复出现的同伦类型论（HoTT）Lean4 代码片段。

## 1. 圆的定义 (Circle / $S^1$)

**规范定义**：圆是同伦类型论中的基本高阶归纳类型，由基点 `base` 和路径 `loop` 生成。

**Lean4 代码**：

```lean
inductive S1 : Type where
  | base : S1
  | loop : base = base
```

**说明**：

- `base` 是圆上的一个点。
- `loop` 是从 `base` 到 `base` 的非平凡路径，对应圆的一周。
- 圆的环路空间 $\Omega(S^1, \text{base})$ 等价于整数群 $\mathbb{Z}$。

**引用来源**：`docs/05-类型理论/03-同伦类型论.md`

---

## 2. 球面的定义 (Sphere / $S^2$)

**规范定义**：二维球面由基点 `base` 和二维路径 `surf` 生成。

**Lean4 代码**：

```lean
inductive S2 : Type where
  | base : S2
  | surf : Id (Id.base base base) (refl base) (refl base)
```

**说明**：

- `surf` 是填充在 `refl base` 与自身之间的二维面（2-path）。
- 等价于在恒等路径上引入一个高阶回路。

**引用来源**：`docs/05-类型理论/03-同伦类型论.md`
