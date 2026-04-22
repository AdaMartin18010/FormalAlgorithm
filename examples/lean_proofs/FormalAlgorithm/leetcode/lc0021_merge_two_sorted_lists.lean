/-
  lc0021_merge_two_sorted_lists.lean
  LeetCode 21. 合并两个有序链表的形式化证明（Lean 4）

  证明目标：
    1. 定义有序链表的形式化模型。
    2. 实现递归合并算法。
    3. 证明合并结果的有序性（输出保持非递减）。
    4. 证明合并结果的元素多重集等于输入多重集之并（元素守恒）。
    5. 证明算法的终止性。

  依赖: Mathlib4 的列表、排序与多重集工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/06-双指针.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Multiset.Basic
import Mathlib.Tactic

open Nat List

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 用列表模拟链表节点（值类型为 α）。 -/
abbrev LinkedList (α : Type) := List α

/-- 列表是非递减有序的。 -/
def IsSorted {α : Type} [LE α] [DecidableRel (@LE.le α _)] (xs : List α) : Prop :=
  xs.Sorted (· ≤ ·)

/-- 合并两个有序链表的递归实现。
    对应 LeetCode 21 的标准递归解法。 -/
def mergeTwoLists {α : Type} [LE α] [DecidableRel (@LE.le α _)] (l1 l2 : List α) : List α :=
  match l1, l2 with
  | [], l2 => l2
  | l1, [] => l1
  | x :: xs, y :: ys =>
      if x ≤ y then
        x :: mergeTwoLists xs (y :: ys)
      else
        y :: mergeTwoLists (x :: xs) ys
  termination_by l1.length + l2.length
  decreasing_by
    all_goals
      simp_wf
      <;> try omega

-- ============================================================
-- 2. 核心定理：递归正确性
-- ============================================================

/-- 定理 1（输出有序性）：若输入链表 l1 和 l2 均为非递减有序，
    则 mergeTwoLists l1 l2 也是非递减有序的。

    证明思路（结构归纳法）：
    - 基础：若 l1 或 l2 为空，结果即为另一链表，有序性 trivial。
    - 归纳：设 l1 = x::xs, l2 = y::ys 且两者均有序。
      若 x ≤ y：结果为 x :: mergeTwoLists xs (y::ys)。
        · x ≤ mergeTwoLists xs (y::ys) 的首元素：
           因为 xs 有序且首元素 ≥ x（若 xs 非空），
           或 y::ys 首元素 = y ≥ x。
         · 由归纳假设，mergeTwoLists xs (y::ys) 有序。
         · 因此 x :: ... 有序。
      若 x > y：对称情况。 -/
theorem mergeTwoLists_preserves_sorted
    {α : Type} [LinearOrder α]
    (l1 l2 : List α)
    (h1 : IsSorted l1)
    (h2 : IsSorted l2)
    : IsSorted (mergeTwoLists l1 l2) := by
  sorry -- TODO: 对 l1.length + l2.length 使用归纳法，分情况讨论

/-- 定理 2（元素守恒）：mergeTwoLists 的结果包含的元素多重集
    恰好等于 l1 和 l2 的元素多重集之并（无增删改）。

    证明思路（结构归纳法）：
    - 基础：空列表情况 trivial。
    - 归纳：每次递归将较小元素放入结果，并从对应列表中移除该元素。
      由归纳假设，递归结果的多重集等于剩余子列表的多重集之并。
      加上当前取出的元素，恰好等于原始两列表的多重集之并。 -/
theorem mergeTwoLists_multiset_eq
    {α : Type} [LE α] [DecidableRel (@LE.le α _)]
    (l1 l2 : List α)
    : (mergeTwoLists l1 l2 : Multiset α) = (l1 : Multiset α) + (l2 : Multiset α) := by
  sorry -- TODO: 使用 Multiset 归纳法，利用 mergeTwoLists 的结构展开

/-- 定理 3（结果长度）：合并结果的长度等于两个输入长度之和。 -/
theorem mergeTwoLists_length
    {α : Type} [LE α] [DecidableRel (@LE.le α _)]
    (l1 l2 : List α)
    : (mergeTwoLists l1 l2).length = l1.length + l2.length := by
  sorry -- TODO: 对 l1.length + l2.length 归纳，展开 mergeTwoLists 定义

/-- 定理 4（终止性）：mergeTwoLists 对任意有限列表必在有限步内终止。

    证明思路：
    - 度量函数为 l1.length + l2.length。
    - 每次递归调用至少从一个列表中移除一个元素，
      因此度量严格递减。
    - 度量下界为 0，故不存在无限递降链。 -/
theorem mergeTwoLists_terminates
    {α : Type} [LE α] [DecidableRel (@LE.le α _)]
    (l1 l2 : List α)
    : Acc (fun (p q : List α × List α) => p.1.length + p.2.length < q.1.length + q.2.length) (l1, l2) := by
  sorry -- TODO: 利用长度度量的良基性证明 Acc 关系

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：若 x ≤ y 且 y ≤ z，则 x ≤ z（传递性，可直接用 LinearOrder 的 le_trans）。
    这里显式写出作为合并有序性证明的辅助。 -/
theorem sorted_head_le_merge_tail
    {α : Type} [LinearOrder α]
    (x : α) (xs l2 : List α)
    (h_x_le : ∀ y ∈ xs, x ≤ y)
    (h_sorted : IsSorted (mergeTwoLists xs l2))
    (h_head : ∀ z ∈ mergeTwoLists xs l2, xs.head? = some x → x ≤ z)
    : IsSorted (x :: mergeTwoLists xs l2) := by
  sorry -- TODO: 验证 x 不大于结果列表的任何元素

/-- 引理：非递减列表的尾部仍为非递减。 -/
theorem sorted_tail
    {α : Type} [LinearOrder α]
    (x : α) (xs : List α)
    (h_sorted : IsSorted (x :: xs))
    : IsSorted xs := by
  sorry -- TODO: 展开 Sorted 定义，利用 List.Pairwise 的性质

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! mergeTwoLists [1, 2, 4] [1, 3, 4]    -- 期望: [1, 1, 2, 3, 4, 4]
#eval! mergeTwoLists ([] : List Nat) ([] : List Nat)  -- 期望: []
#eval! mergeTwoLists [0] [0]                -- 期望: [0, 0]
#eval! mergeTwoLists [-10, -5, 0] [-3, 5, 10]  -- 期望: [-10, -5, -3, 0, 5, 10]

#check mergeTwoLists_preserves_sorted
#check mergeTwoLists_multiset_eq
