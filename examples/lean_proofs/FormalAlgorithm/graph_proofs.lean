/-
FormalAlgorithm Lean Proof Status: wip
Sorry Count: 4
Last Audited: 2026-04-29
Notes: BFS 可达性完备性与访问唯一性定理为 sorry 占位
-/

/-
  graph_proofs.lean
  图遍历基本性质的形式化证明（Lean 4）

  证明目标：
  1. BFS 从起点出发，访问到的所有节点都是从起点可达的。
  2. 若一个节点从起点可达且图是有限的，则 BFS 会将其标记为已访问。

  本证明使用 Lean 4 标准库，不依赖 mathlib4。
  为简化形式化，我们将图表示为邻接函数：每个节点映射到一个节点列表。
-/

-- 简化的图表示：节点类型为 Nat，邻接关系由函数给出
abbrev Graph := Nat → List Nat

-- BFS 的辅助定义：维护一个已访问集合和一个待探索队列。
-- 由于 queue 长度可能增加（加入新邻居），Lean 4 的自动终止检查器
-- 无法直接识别其终止性。我们使用 partial 声明，这在算法验证中很常见。
partial def bfs_aux (g : Graph) (visited : List Nat) (queue : List Nat) : List Nat :=
  match queue with
  | [] => visited
  | q :: qs =>
    let neighbors := g q
    let new_nodes := neighbors.filter (λ n => ¬ visited.contains n)
    bfs_aux g (visited ++ new_nodes) (qs ++ new_nodes)

-- BFS 入口
def bfs (g : Graph) (start : Nat) : List Nat :=
  bfs_aux g [start] [start]

-- 定义"节点 target 从 start 在图 g 中可达"
inductive Reachable (g : Graph) (start : Nat) : Nat → Prop where
  | refl : Reachable g start start
  | step {u v : Nat} : Reachable g start u → v ∈ g u → Reachable g start v

-- 证明义务 PO-003：BFS 访问的节点都是可达的
-- 定理：BFS 访问的每个节点都是从起点可达的。
--
-- 证明思路（需将 bfs_aux 重构为 well-founded 递归 + mathlib4 有限集工具）：
-- 1. 将 bfs_aux 从 partial def 重构为 well-founded 递归。
--    度量：有限图中未访问节点的数量（或队列长度与已访问集合大小的组合）。
--    依赖前提：图是有限的（存在有限节点列表包含所有可达节点）。
-- 2. 对 bfs_aux 的递归结构进行归纳，维护不变式：
--    - queue 中的所有节点都从 start 可达；
--    - visited 中的所有节点都从 start 可达；
--    - 新加入的 new_nodes = neighbors.filter (¬visited.contains) 是 queue 头节点 q 的邻居，
--      由 Reachable.step 可知它们也可达。
-- 3. 当 queue 为空时，bfs_aux 返回 visited，此时 visited 中所有节点都满足 Reachable。
--
-- 依赖外部工具：
--   - mathlib4 的 `Finset` / `Set.Finite` 用于表达"有限图"
--   - `WellFounded` 引理用于 well-founded 递归的终止性证明
--
-- 当前使用 sorry 占位，待环境具备后替换为实际证明。
theorem bfs_visits_only_reachable (g : Graph) (start : Nat)
    : ∀ n, n ∈ bfs g start → Reachable g start n := by
  intro n hn
  simp [bfs] at hn
  sorry

-- 证明义务 PO-004：BFS 完备性（有限图）
-- 定理：若图是有限的且节点从起点可达，则 BFS 会将其标记为已访问。
--
-- 证明思路（需 mathlib4 的有限集 / well-founded 工具）：
-- 1. 利用 h_finite 获取所有可达节点的有限列表 nodes。
-- 2. 定义距离函数 distance(g, start, v) = 从 start 到 v 的最短路径长度（边数）。
--    在有限无负权环的图中，该距离是良定义的有限自然数。
-- 3. 对 distance(g, start, target) 进行归纳：
--    - 基例 d=0：target = start，显然 start ∈ bfs g start（由 bfs 定义）。
--    - 归纳步骤：假设对所有距离 < d 的节点，BFS 都会访问。
--      若 target 距离为 d，则存在前驱节点 pred 使得 distance(pred) = d-1
--      且 target ∈ g pred。
--      由归纳假设 pred 被访问，在 BFS 处理 pred 时，target 作为邻居被加入 queue，
--      因此最终会被访问。
-- 4. BFS 的按层扩展性质保证了上述归纳的有效性。
--
-- 依赖外部工具：
--   - mathlib4 的 `Finset` / `Set.Finite` 用于处理有限节点集
--   - `WellFounded` 或 `Nat.measure` 用于最短路径长度的归纳
--   - `List.Subset` / `List.Nodup` 用于已访问集合的性质推导
--
-- 当前使用 sorry 占位，待环境具备后替换为实际证明。
theorem bfs_visits_all_reachable_finite
    (g : Graph)
    (start : Nat)
    (target : Nat)
    (h_finite : ∃ (nodes : List Nat), ∀ n, Reachable g start n → n ∈ nodes)
    (h_reach : Reachable g start target)
    : target ∈ bfs g start := by
  sorry

-- 示例验证
#eval bfs (λ n => match n with | 0 => [1, 2] | 1 => [3] | 2 => [3] | _ => []) 0
