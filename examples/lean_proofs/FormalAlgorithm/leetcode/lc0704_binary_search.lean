/-
  lc0704_binary_search.lean
  LeetCode 704. 二分查找正确性的形式化证明（Lean 4）

  证明目标：
    1. 若 target 在有序数组 nums 中，search 返回其索引。
    2. 若 target 不在 nums 中，search 返回 -1。
    3. 算法必终止。

  依赖: Mathlib4 的序理论和自然数工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/05-二分查找.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Order.Basic

open Nat

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 安全列表索引，返回 Option 值。 -/
def listGet? {α : Type} (xs : List α) (i : Nat) : Option α :=
  match xs, i with
  | [], _ => none
  | x :: _, 0 => some x
  | _ :: xs', i+1 => listGet? xs' i

/-- 数组是有序的（非递减）。-/
def IsSorted (nums : List Int) : Prop :=
  match nums with
  | [] => True
  | [_] => True
  | x :: y :: zs => x ≤ y ∧ IsSorted (y :: zs)

/-- target 在数组 nums 中的索引 i 处。-/
def IsAtIndex (nums : List Int) (target : Int) (i : Nat) : Prop :=
  listGet? nums i = some target

/-- target 存在于数组 nums 中。-/
def ExistsIn (nums : List Int) (target : Int) : Prop :=
  ∃ i : Nat, IsAtIndex nums target i

-- ============================================================
-- 2. 二分查找函数的 Lean 实现（规范描述）
-- ============================================================

/-- 二分查找的纯函数实现。
    返回 target 在有序数组 nums 中的索引，若不存在则返回 -1。
    使用递归模拟循环，以区间长度作为 well-founded 度量。 -/
def binarySearch (nums : List Int) (target : Int) (left right : Nat) : Int :=
  if left > right then
    -1
  else
    let mid := left + (right - left) / 2
    match listGet? nums mid with
    | none => -1
    | some midVal =>
      if midVal == target then
        mid
      else if midVal < target then
        binarySearch nums target (mid + 1) right
      else
        if h : mid > 0 then
          binarySearch nums target left (mid - 1)
        else
          -1
termination_by right - left + 1
decreasing_by
  all_goals
    sorry -- TODO: 证明新区间长度严格递减以保证终止性

/-- 对外的包装函数，初始搜索区间为整个数组。 -/
def binarySearchFull (nums : List Int) (target : Int) : Int :=
  binarySearch nums target 0 (nums.length)

-- ============================================================
-- 3. 循环不变式的形式化陈述
-- ============================================================

/-- 二分查找的循环不变式。
    在搜索区间 [left, right] 上，若 target 存在于 nums 中，
    则其索引必然落在 [left, right] 范围内（闭区间）。 -/
def LoopInvariant (nums : List Int) (target : Int) (left right : Nat) : Prop :=
  ∀ i : Nat, IsAtIndex nums target i → left ≤ i ∧ i ≤ right

-- ============================================================
-- 4. 核心定理
-- ============================================================

/-- 定理 1（存在性）：若 target 在有序数组 nums 中，
    且初始区间覆盖整个数组，则 binarySearchFull 返回其索引。

    证明思路：
    - 对区间长度使用 well-founded 归纳。
    - 利用循环不变式保持性：每次迭代后新区间仍包含目标索引。
    - 当 midVal == target 时直接返回 mid。
    - 当区间为空时，由不变式的逆否命题知 target 不存在（与假设矛盾）。 -/
theorem binary_search_found
    (nums : List Int) (target : Int)
    (h_sorted : IsSorted nums)
    (h_exists : ExistsIn nums target)
    : ∃ i : Nat, binarySearchFull nums target = i ∧ IsAtIndex nums target i := by
  sorry -- TODO: 使用 well-founded 归纳与循环不变式完成证明

/-- 定理 2（否定性）：若 target 不在有序数组 nums 中，
    则 binarySearchFull 返回 -1。

    证明思路：
    - 对区间长度使用 well-founded 归纳。
    - 利用循环不变式：若区间为空且不变式成立，则 target 不存在。
    - 由于 target 不存在，不变式的前件永假，故不变式平凡成立。
    - 最终到达 left > right 分支，返回 -1。 -/
theorem binary_search_not_found
    (nums : List Int) (target : Int)
    (h_sorted : IsSorted nums)
    (h_not_exists : ¬ExistsIn nums target)
    : binarySearchFull nums target = -1 := by
  sorry -- TODO: 利用不变式在区间为空时的逆否命题完成证明

/-- 定理 3（终止性）：binarySearch 对任意输入必在有限步内终止。

    证明思路：
    - 以区间长度 `right - left + 1` 作为 well-founded 度量。
    - 当 midVal < target 时，left 更新为 mid + 1，新区间长度严格减小。
    - 当 midVal > target 时，right 更新为 mid - 1，新区间长度严格减小。
    - 当 midVal == target 时直接返回。
    - 因此不存在无限递降链，算法必终止。 -/
theorem binary_search_terminates
    (nums : List Int) (target : Int) (left right : Nat)
    : Acc (fun (p q : Nat × Nat) => p.2 - p.1 < q.2 - q.1) (left, right) := by
  sorry -- TODO: 以区间长度作为 well-founded 度量，证明 Acc 关系

-- ============================================================
-- 5. 辅助引理（证明骨架）
-- ============================================================

/-- 引理：若 nums 是有序的，且 midVal < target，
    则 target 若在数组中，其索引必大于 mid。

    这是将搜索区间移至右半部分的依据。 -/
theorem sorted_implies_target_gt_mid
    (nums : List Int) (target : Int) (mid : Nat) (midVal : Int)
    (h_sorted : IsSorted nums)
    (h_lt : listGet? nums mid = some midVal ∧ midVal < target)
    (h_exists : ExistsIn nums target)
    : ∀ i : Nat, IsAtIndex nums target i → i > mid := by
  sorry -- TODO: 利用有序性传递性证明

/-- 引理：若 nums 是有序的，且 midVal > target，
    则 target 若在数组中，其索引必小于 mid。

    这是将搜索区间移至左半部分的依据。 -/
theorem sorted_implies_target_lt_mid
    (nums : List Int) (target : Int) (mid : Nat) (midVal : Int)
    (h_sorted : IsSorted nums)
    (h_gt : listGet? nums mid = some midVal ∧ midVal > target)
    (h_exists : ExistsIn nums target)
    : ∀ i : Nat, IsAtIndex nums target i → i < mid := by
  sorry -- TODO: 利用有序性传递性证明

-- ============================================================
-- 6. 示例验证（非形式化测试）
-- ============================================================

#eval! binarySearchFull [-1, 0, 3, 5, 9, 12] 9   -- 期望: 4
#eval! binarySearchFull [-1, 0, 3, 5, 9, 12] 2   -- 期望: -1
#eval! binarySearchFull [5] 5                      -- 期望: 0
#eval! binarySearchFull ([] : List Int) 1          -- 期望: -1
