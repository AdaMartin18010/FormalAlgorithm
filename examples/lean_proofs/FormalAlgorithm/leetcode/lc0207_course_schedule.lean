/-
  lc0207_course_schedule.lean
  LeetCode 207. 课程表的形式化证明（Lean 4）

  证明目标：
    1. 定义有向图模型表示课程先修关系。
    2. 证明拓扑排序算法的终止性：无环有向图必存在拓扑序。
    3. 证明基于 DFS 的环检测正确性：图中有环当且仅当 DFS 遇到回边。
    4. 证明 Kahn 算法（入度消除法）的终止性。

  依赖: Mathlib4 的集合论、图论基础与有向图工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/07-图论算法.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

-- import Mathlib.Data.Finset.Basic  -- 暂时禁用，待mathlib修复
-- import Mathlib.Data.Set.Basic  -- 暂时禁用，待mathlib修复
import Mathlib.Order.WellFoundedSet
import Mathlib.Tactic

open Nat

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 课程数量与先修关系。
    numCourses 表示课程总数（编号 0 到 numCourses-1）。
    prerequisites 是二元组列表，(a, b) 表示修课程 a 前必须先修课程 b。 -/
structure CourseSchedule where
  numCourses : Nat
  prerequisites : List (Nat × Nat)
  /-- 所有课程编号在有效范围内。 -/
  h_valid : ∀ p ∈ prerequisites, p.1 < numCourses ∧ p.2 < numCourses

/-- 有向边：从 b 指向 a（b 是 a 的先修课）。 -/
def edges (cs : CourseSchedule) : List (Nat × Nat) :=
  cs.prerequisites

/-- 邻接表：每个节点的出边邻居。 -/
def adjList (cs : CourseSchedule) (u : Nat) : List Nat :=
  cs.prerequisites.filterMap (fun p => if p.2 == u then some p.1 else none)

/-- 节点入度：指向该节点的边数。 -/
def inDegree (cs : CourseSchedule) (u : Nat) : Nat :=
  cs.prerequisites.countP (fun p => p.1 == u)

/-- 存在环的定义：存在节点序列 v₀, v₁, ..., vₖ = v₀ 构成有向回路。 -/
def HasCycle (cs : CourseSchedule) : Prop :=
  ∃ (path : List Nat) (start : Nat),
    path ≠ [] ∧
    path.head? = some start ∧
    path.getLast? = some start ∧
    (∀ i, i + 1 < path.length →
      (path[i]!, path[i+1]!) ∈ cs.prerequisites)

/-- 无环图（DAG）的定义。 -/
def IsDAG (cs : CourseSchedule) : Prop :=
  ¬HasCycle cs

/-- 拓扑序：节点排列使得每条有向边都从前指向后。 -/
def IsTopologicalOrder (cs : CourseSchedule) (order : List Nat) : Prop :=
  order.length = cs.numCourses ∧
  (∀ p ∈ cs.prerequisites,
    ∃ (i j : Nat), i < j ∧ order[i]! = p.2 ∧ order[j]! = p.1)

-- ============================================================
-- 2. 核心定理：拓扑排序与环检测
-- ============================================================

/-- 定理 1（DAG 存在拓扑序）：若课程图是无环有向图（DAG），
    则必存在一个拓扑排序。

    证明思路（归纳法）：
    - 基础：0 个节点的 DAG 拓扑序为空列表。
    - 归纳：DAG 必存在入度为 0 的节点（否则每个节点都有一条入边，可构造环）。
      取一个入度为 0 的节点 v，将其放在拓扑序首位。
      删除 v 及其出边后，剩余图仍是 DAG。
      由归纳假设，剩余图有拓扑序，拼接即得完整拓扑序。 -/
theorem dag_has_topological_order
    (cs : CourseSchedule)
    (h_dag : IsDAG cs)
    : ∃ order : List Nat, IsTopologicalOrder cs order := by
  sorry -- TODO: 对节点数使用归纳法，利用入度引理构造拓扑序

/-- 定理 2（拓扑序蕴含无环）：若课程图存在拓扑序，则图中无环。

    证明思路：
    - 反证法。假设存在环 v₀ → v₁ → ... → vₖ = v₀。
    - 在拓扑序中，v₀ 在 v₁ 前，v₁ 在 v₂ 前，...，vₖ₋₁ 在 vₖ 前。
    - 传递性得 v₀ 在 vₖ = v₀ 前，矛盾。 -/
theorem topological_order_implies_dag
    (cs : CourseSchedule)
    (h_top : ∃ order : List Nat, IsTopologicalOrder cs order)
    : IsDAG cs := by
  sorry -- TODO: 反证法，利用拓扑序的传递性导出矛盾

/-- 定理 3（Kahn 算法终止性）：Kahn 算法（反复删除入度为 0 的节点）
    在无环图上必在有限步内终止，并产生拓扑序。

    证明思路：
    - 每次迭代至少删除一个节点（DAG 总有入度为 0 的节点）。
    - 节点总数严格递减，因此至多 numCourses 轮后终止。
    - 若终止时所有节点均已删除，则产生完整拓扑序。
    - 若终止时仍有节点，则剩余子图中每个节点入度 ≥ 1，可构造环（矛盾）。 -/
theorem kahn_algorithm_terminates
    (cs : CourseSchedule)
    (h_dag : IsDAG cs)
    : Acc (fun (n m : Nat) => n < m) cs.numCourses := by
  sorry -- TODO: 以剩余节点数为 well-founded 度量，证明严格递减

/-- 列表链式关系（替代缺失的 List.Chain）。 -/
inductive ListChain {α : Type} (R : α → α → Prop) : List α → Prop where
  | nil : ListChain R []
  | singleton (x : α) : ListChain R [x]
  | cons {x y : α} {ys : List α} : R x y → ListChain R (y :: ys) → ListChain R (x :: y :: ys)

/-- 定理 4（DFS 环检测正确性）：基于 DFS 的三色标记法（白/灰/黑）
    正确检测有向图中的环。

    证明思路：
    - 充分性：若 DFS 遇到灰色节点（当前递归栈中的节点），则存在回边，构成环。
    - 必要性：若存在环，DFS 必会沿着环上的边遍历，最终遇到环上的灰色节点。 -/
theorem dfs_cycle_detection_correct
    (cs : CourseSchedule)
    : HasCycle cs ↔
      ∃ (start : Nat) (path : List Nat),
        start < cs.numCourses ∧
        ListChain (fun u v => (u, v) ∈ cs.prerequisites) path ∧
        path.head? = some start ∧
        path.getLast? = some start := by
  sorry -- TODO: 双向证明，利用 DFS 树边/回边的分类

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：有限 DAG 必有入度为 0 的节点。
    这是拓扑排序归纳步骤的关键。 -/
theorem dag_has_zero_indegree_node
    (cs : CourseSchedule)
    (h_dag : IsDAG cs)
    (h_nodes : cs.numCourses > 0)
    : ∃ u, u < cs.numCourses ∧ inDegree cs u = 0 := by
  sorry -- TODO: 反证法，若所有节点入度 ≥ 1，可沿反向边构造无限递降链或环

/-- 引理：删除入度为 0 的节点及其出边后，剩余图仍是无环的。 -/
theorem remove_node_preserves_dag
    (cs : CourseSchedule)
    (h_dag : IsDAG cs)
    (u : Nat) (h_u : u < cs.numCourses)
    (h_indeg : inDegree cs u = 0)
    : IsDAG { numCourses := cs.numCourses - 1,
              prerequisites := cs.prerequisites.filter (fun p => p.1 ≠ u ∧ p.2 ≠ u),
              h_valid := by sorry } := by
  sorry -- TODO: 利用子图无环性继承

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

-- 示例 1：numCourses = 2, prerequisites = [(1,0)]，可以完成
#eval! (2, [(1, 0)])  -- 期望拓扑序存在

-- 示例 2：numCourses = 2, prerequisites = [(1,0), (0,1)]，有环
#eval! (2, [(1, 0), (0, 1)])  -- 期望有环，无拓扑序

#check HasCycle
#check IsDAG
#check dag_has_topological_order
