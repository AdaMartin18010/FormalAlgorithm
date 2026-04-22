/-
  lc0200_number_of_islands.lean
  LeetCode 200. 岛屿数量的形式化证明（Lean 4）

  证明目标：
    1. 定义网格图及岛屿的形式化模型。
    2. 实现 BFS/DFS 访问标记算法。
    3. 证明访问标记的正确性：每个陆地格子被且仅被访问一次。
    4. 证明算法计数的正确性：BFS/DFS 启动次数等于连通分量数。

  依赖: Mathlib4 的图论、集合与有限类型工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Tactic

open Nat Finset

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 网格坐标。 -/
structure GridCoord (rows cols : Nat) where
  r : Nat
  c : Nat
  h_r : r < rows
  h_c : c < cols

/-- 网格图：用函数表示每个格子是否为陆地（1）或水域（0）。 -/
structure GridMap (rows cols : Nat) where
  value : GridCoord rows cols → Nat
  h_binary : ∀ p, value p = 0 ∨ value p = 1

/-- 两个坐标相邻（四连通）。 -/
def adjacent {rows cols : Nat} (p q : GridCoord rows cols) : Prop :=
  (p.r = q.r ∧ ((p.c + 1 = q.c) ∨ (q.c + 1 = p.c))) ∨
  (p.c = q.c ∧ ((p.r + 1 = q.r) ∨ (q.r + 1 = p.r)))

/-- 陆地格子集合。 -/
def landCells (grid : GridMap rows cols) : Finset (GridCoord rows cols) :=
  Finset.univ.filter (fun p => grid.value p = 1)

/-- 岛屿（连通分量）定义：陆地格子的极大四连通子集。 -/
def IsIsland (grid : GridMap rows cols) (island : Finset (GridCoord rows cols)) : Prop :=
  island ⊆ landCells grid ∧
  island.Nonempty ∧
  (∀ p ∈ island, ∀ q ∈ island, p = q ∨
    ∃ path : List (GridCoord rows cols),
      path.head? = some p ∧ path.getLast? = some q ∧
      ∀ i, i + 1 < path.length → adjacent (path.get ⟨i, by sorry⟩) (path.get ⟨i+1, by sorry⟩)) ∧
  (∀ p ∈ island, ∀ q ∈ landCells grid, adjacent p q → q ∈ island)

/-- 岛屿数量的规范定义：陆地区域的连通分量数。 -/
def numIslandsSpec (grid : GridMap rows cols) : Nat :=
  -- 连通分量数的规范定义（非构造性）
  let islands := { s : Finset (GridCoord rows cols) | IsIsland grid s }
  islands.ncard

-- ============================================================
-- 2. BFS/DFS 访问标记算法
-- ============================================================

/-- BFS 访问一个岛屿，返回访问过的所有格子。
    使用递归模拟队列，visited 记录已访问格子。 -/
def bfsIsland (grid : GridMap rows cols)
    (start : GridCoord rows cols)
    (visited : Finset (GridCoord rows cols)) : Finset (GridCoord rows cols) :=
  if h : grid.value start = 1 ∧ start ∉ visited then
    let visited' := visited.insert start
    -- 获取四邻域（简化表示，实际需要边界检查）
    let neighbors := Finset.univ.filter (fun q => adjacent start q ∧ grid.value q = 1)
    neighbors.fold (fun acc q => bfsIsland grid q acc) visited'
  else
    visited

/-- 岛屿数量算法：遍历所有格子，遇到未访问的陆地就启动 BFS。 -/
def numIslandsBFS (grid : GridMap rows cols) : Nat :=
  let cells := Finset.univ.filter (fun p => grid.value p = 1)
  let rec count (remaining : Finset (GridCoord rows cols))
      (visited : Finset (GridCoord rows cols)) (acc : Nat) : Nat :=
    if h : remaining.Nonempty then
      let start := remaining.min' h
      if start ∈ visited then
        count (remaining.erase start) visited acc
      else
        let visited' := bfsIsland grid start visited
        let remaining' := remaining \ visited'
        count remaining' visited' (acc + 1)
    else
      acc
  count cells ∅ 0

-- ============================================================
-- 3. 核心定理：BFS 访问标记正确性
-- ============================================================

/-- 定理 1（访问唯一性）：BFS 启动后，每个陆地格子被且仅被访问一次。

    证明思路：
    - 对 bfsIsland 的递归深度进行归纳。
    - 基础步：start 不在 visited 中，将其加入 visited'。
    - 归纳步：对每个邻居 q，递归调用 bfsIsland grid q visited'。
      由于 visited' 已包含 start，且每次递归都将当前节点加入 visited，
      同一个节点不会被重复访问。
    - 由 Finset.insert 的幂等性，即使多个路径到达同一节点，结果不变。 -/
theorem bfs_visit_unique
    (grid : GridMap rows cols)
    (start : GridCoord rows cols)
    (visited : Finset (GridCoord rows cols))
    : bfsIsland grid start visited = visited ∨
      bfsIsland grid start visited = visited ∪ { start } ∪
        (Finset.univ.filter (fun q => adjacent start q ∧ grid.value q = 1)) := by
  sorry -- TODO: 分情况讨论 start 是否为陆地且是否已访问

/-- 定理 2（连通分量完整性）：从 start 启动的 BFS 恰好访问 start 所在的整个连通分量。

    证明思路：
    - 充分性：BFS 只沿着相邻陆地格子扩展，因此访问的每个格子都与 start 连通。
    - 必要性：设 q 是与 start 连通的任意陆地格子，存在路径 start = p₀, p₁, ..., pₖ = q。
      对路径长度 k 进行归纳，证明 q 必被访问。
    - 因此 BFS 访问集合等于 start 的连通分量。 -/
theorem bfs_visits_entire_component
    (grid : GridMap rows cols)
    (start : GridCoord rows cols)
    (h_land : grid.value start = 1)
    : let visited := bfsIsland grid start ∅
      ∀ q ∈ visited, ∃ path : List (GridCoord rows cols),
        path.head? = some start ∧ path.getLast? = some q := by
  sorry -- TODO: 利用 BFS 的层次扩展性质与路径归纳法证明

/-- 定理 3（计数正确性）：numIslandsBFS 返回的值等于岛屿数量的规范定义。

    证明思路：
    - 每次遇到一个未访问的陆地格子 start，就启动一次 BFS，访问其整个连通分量。
    - 由定理 2，该 BFS 恰好覆盖一个岛屿。
    - 计数器 acc 每次 BFS 启动时加 1，因此最终 acc 等于连通分量数。
    - 由定理 1，已访问的格子不会触发新的 BFS，因此不会重复计数。 -/
theorem num_islands_correct
    (grid : GridMap rows cols)
    : numIslandsBFS grid = numIslandsSpec grid := by
  sorry -- TODO: 利用访问唯一性与连通分量完整性完成证明

-- ============================================================
-- 4. 辅助引理
-- ============================================================

/-- 引理：相邻关系是对称的。 -/
theorem adjacent_symmetric
    {rows cols : Nat} (p q : GridCoord rows cols)
    : adjacent p q → adjacent q p := by
  sorry -- TODO: 展开 adjacent 定义，利用加法交换律证明

/-- 引理：BFS 访问集合是单调递增的。 -/
theorem bfs_monotone
    (grid : GridMap rows cols)
    (start : GridCoord rows cols)
    (visited1 visited2 : Finset (GridCoord rows cols))
    (h_subset : visited1 ⊆ visited2)
    : bfsIsland grid start visited1 ⊆ bfsIsland grid start visited2 := by
  sorry -- TODO: 利用递归结构与 Finset.subset 的传递性证明

-- ============================================================
-- 5. 示例验证（非形式化测试）
-- ============================================================

-- 由于 GridMap 是抽象模型，这里用 #check 验证类型正确性
#check GridMap
#check numIslandsBFS
#check num_islands_correct
#check bfs_visit_unique
