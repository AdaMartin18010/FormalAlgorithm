/-
  lc0141_linked_list_cycle.lean
  LeetCode 141. 环形链表的形式化证明（Lean 4）

  证明目标：
    1. 定义链表及环的形式化模型。
    2. 实现 Floyd 判环算法（快慢指针）。
    3. 证明：若链表中存在环，则快指针（每次走 2 步）与慢指针（每次走 1 步）必相遇。
    4. 证明：若链表中无环，则快指针必到达链表末尾（nil）。

  依赖: Mathlib4 的自然数模运算与数论工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Ring.Int
import Mathlib.Data.Finset.Basic

open Nat

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 用函数模型表示链表：每个节点有一个整数值和下一个节点的索引。
    用函数 next : Nat → Option Nat 表示后继关系。
    None 表示链表终止（无环时）或节点不存在。 -/
structure LinkedList (maxNodes : Nat) where
  /-- 节点值函数 -/
  value : Fin maxNodes → Int
  /-- 后继函数，None 表示无后继 -/
  next : Fin maxNodes → Option (Fin maxNodes)

/-- 链表节点序列：从 start 出发沿着 next 走 n 步到达的节点。 -/
def LinkedList.traverse (ll : LinkedList maxNodes) (start : Fin maxNodes) : Nat → Option (Fin maxNodes)
  | 0 => some start
  | n + 1 => match ll.traverse start n with
      | none => none
      | some node => ll.next node

/-- 存在环的定义：存在某个起始节点和步数 k > 0，使得从该节点出发走 k 步后回到自身。 -/
def HasCycle (ll : LinkedList maxNodes) : Prop :=
  ∃ (start : Fin maxNodes) (k : Nat), k > 0 ∧ ll.traverse start k = some start

/-- 无环的定义：对任意起始节点，经过 maxNodes 步后必到达 None（因为节点数有限）。 -/
def NoCycle (ll : LinkedList maxNodes) : Prop :=
  ∀ (start : Fin maxNodes), ll.traverse start maxNodes = none

/-- Floyd 判环算法：快慢指针。
    slow 每次走 1 步，fast 每次走 2 步。
    若 fast 到达 None，则无环；若 slow = fast 且非起点，则有环。 -/
partial def floydCycleDetection (ll : LinkedList maxNodes) (slow fast : Fin maxNodes) : Bool :=
  match ll.next slow, ll.next fast with
  | some s, some f1 =>
      match ll.next f1 with
      | some f2 =>
          if s = f2 then true
          else floydCycleDetection ll s f2
      | none => false
  | _, _ => false

-- ============================================================
-- 2. 核心定理：Floyd 判环正确性
-- ============================================================

/-- 定理 1（有环必相遇）：若链表 ll 存在环，则从环上任意节点同时出发的
    慢指针（步长 1）和快指针（步长 2）必在有限步内相遇。

    证明思路：
    - 设环长为 L，快慢指针从环上同一点出发。
    - 慢指针位置：i mod L；快指针位置：2i mod L。
    - 相遇条件：2i ≡ i (mod L) ⟺ i ≡ 0 (mod L)。
    - 取 i = L，则慢指针走了 L 步，快指针走了 2L 步，两者均回到起点，必相遇。
    - 更精细地，考虑非起点出发的情况：设进入环前长度为 μ，环长为 L。
      当慢指针进入环时（走了 μ 步），快指针已在环内走了 2μ 步，位置为 (2μ - μ) mod L = μ mod L。
      此后两者相对速度为 1（快比慢多走 1 步每轮），距离差以每轮 1 的速度缩小，
      因此经过至多 L 轮后距离差为 0，即相遇。 -/
theorem floyd_cycle_implies_meet
    (ll : LinkedList maxNodes)
    (h_cycle : HasCycle ll)
    : ∃ (slow fast : Fin maxNodes) (steps : Nat),
      steps > 0 ∧
      ll.traverse slow steps = ll.traverse fast (2 * steps) := by
  sorry -- TODO: 利用模运算与鸽巢原理构造相遇步数

/-- 定理 2（无环不相遇）：若链表 ll 无环，则 Floyd 算法的快指针必在有限步内到达 None。

    证明思路：
    - 无环链表是有限 DAG，最长路径长度不超过 maxNodes - 1。
    - 快指针每次走 2 步，至多 maxNodes / 2 轮后到达末尾 None。
    - 因此 floydCycleDetection 返回 false。 -/
theorem floyd_no_cycle_reaches_end
    (ll : LinkedList maxNodes)
    (h_no_cycle : NoCycle ll)
    (start : Fin maxNodes)
    : ∃ steps : Nat, steps ≤ maxNodes ∧ ll.traverse start (2 * steps) = none := by
  sorry -- TODO: 利用无环定义与 traverse 的单调性证明

/-- 定理 3（Floyd 算法正确性）：floydCycleDetection 返回 true 当且仅当链表存在环。

    证明思路：
    - 充分性：若算法返回 true，则在某步 slow = fast，说明两者相遇，由定理 1 的逆否可知有环。
    - 必要性：若有环，由定理 1 知必相遇，因此算法必在某步返回 true。 -/
theorem floyd_correctness
    (ll : LinkedList maxNodes)
    (start : Fin maxNodes)
    (h_start : ll.next start ≠ none)
    : floydCycleDetection ll start (ll.next start |>.get (by simp_all [Option.ne_none_iff_exists'])) = true ↔
      HasCycle ll := by
  sorry -- TODO: 结合定理 1 和定理 2 完成双向证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：在环长为 L 的环上，从同一点以步长 1 和步长 2 出发，
    经过 L 步后两者均回到原点。 -/
theorem cycle_meet_after_l_steps
    (L : Nat) (h_L : L > 0)
    : ∃ i : Nat, i > 0 ∧ i % L = 0 ∧ (2 * i) % L = 0 := by
  use L
  constructor
  · exact h_L
  · constructor
    · simp
    · rw [Nat.mul_mod_left]
      simp

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

-- 由于链表是抽象模型，这里用 #check 验证类型正确性
#check LinkedList
#check HasCycle
#check floydCycleDetection
#check floyd_correctness
