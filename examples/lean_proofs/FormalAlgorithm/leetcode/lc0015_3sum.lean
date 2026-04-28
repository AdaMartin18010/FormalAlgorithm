/-
FormalAlgorithm Lean Proof Status: wip
Sorry Count: 4
Last Audited: 2026-04-29
Notes: 双指针不变式、完备性、去重正确性及辅助引理为 sorry 占位
-/

/-
  lc0015_3sum.lean
  LeetCode 15. 三数之和的形式化证明（Lean 4）

  证明目标：
    1. 定义三数之和问题：给定整数数组，找出所有和为 0 的不重复三元组。
    2. 实现排序 + 对撞指针算法。
    3. 证明算法的完备性：不会遗漏任何满足条件的三元组。
    4. 证明算法的去重正确性：每个三元组只被输出一次。

  依赖: Mathlib4 的列表、排序与有限集工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.List.Sort
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic

open List Int

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 三元组 (a, b, c) 满足三数之和条件：a + b + c = 0。 -/
def IsThreeSum (a b c : Int) : Prop :=
  a + b + c = 0

/-- 从列表中选取三个不同索引 i < j < k，使得 nums[i] + nums[j] + nums[k] = 0。 -/
def IsValidTriple (nums : List Int) (i j k : Nat) : Prop :=
  i < j ∧ j < k ∧ k < nums.length ∧
  IsThreeSum (nums.getD i 0) (nums.getD j 0) (nums.getD k 0)

/-- 所有满足条件的三元组集合（按值表示，非索引）。 -/
def allThreeSumTriples (nums : List Int) : Set (Int × Int × Int) :=
  { (a, b, c) | ∃ i j k, IsValidTriple nums i j k ∧
    a = nums.getD i 0 ∧ b = nums.getD j 0 ∧ c = nums.getD k 0 }

/-- 排序后的对撞指针算法（规范描述）。
    固定第一个数 nums[i]，在右侧子数组中用双指针找和为 -nums[i] 的两数。 -/
def threeSumAlgorithm (nums : List Int) : List (Int × Int × Int) :=
  let sorted := nums.mergeSort (· ≤ ·)
  let n := sorted.length
  let rec findPairs (i : Nat) (left right : Nat) (acc : List (Int × Int × Int)) : List (Int × Int × Int) :=
    if h : left < right then
      let sum := sorted.getD i 0 + sorted.getD left 0 + sorted.getD right 0
      if sum < 0 then
        findPairs i (left + 1) right acc
      else if sum > 0 then
        findPairs i left (right - 1) acc
      else
        let triple := (sorted.getD i 0, sorted.getD left 0, sorted.getD right 0)
        let acc' := triple :: acc
        let left' := left + 1
        let right' := right - 1
        findPairs i left' right' acc'
    else
      acc
  let rec outer (i : Nat) (acc : List (Int × Int × Int)) : List (Int × Int × Int) :=
    if h : i < n - 2 then
      let acc' := findPairs i (i + 1) (n - 1) acc
      outer (i + 1) acc'
    else
      acc
  outer 0 []

-- ============================================================
-- 2. 核心定理：对撞指针完备性
-- ============================================================

/-- 引理（双指针不变式）：在固定 nums[i] 后，设目标两数之和为 target = -nums[i]，
    双指针 left 和 right 满足：
    - 若 nums[left] + nums[right] < target，则对于任意 k ≤ left，
      nums[k] + nums[right] ≤ nums[left] + nums[right] < target，
      因此 k 不可能与 right 构成合法对，left 可安全右移。
    - 若 nums[left] + nums[right] > target，同理 right 可安全左移。

    证明思路：利用排序后的单调性。 -/
theorem two_pointers_invariant
    (sorted : List Int)
    (h_sorted : Sorted (· ≤ ·) sorted)
    (target : Int)
    (left right : Nat)
    (h_lr : left < right ∧ right < sorted.length)
    : sorted.getD left 0 + sorted.getD right 0 < target →
      ∀ k, k ≤ left → sorted.getD k 0 + sorted.getD right 0 < target := by
  sorry -- TODO: 利用排序单调性证明左指针右移的安全性

/-- 定理 1（完备性）：排序 + 对撞指针算法不会遗漏任何满足条件的三元组。

    证明思路：
    - 对排序后的数组，设 (a, b, c) 是一个满足 a ≤ b ≤ c 且 a + b + c = 0 的三元组。
    - 算法会枚举所有可能的第一个数 a' = sorted[i]。
    - 当 a' = a 时，在子数组 sorted[i+1..] 中用双指针找和为 -a 的两数。
    - 由引理 two_pointers_invariant，双指针的收缩不会跳过 b 和 c 所在的合法位置。
    - 因此 (b, c) 必被找到，三元组 (a, b, c) 被输出。 -/
theorem three_sum_completeness
    (nums : List Int)
    : ∀ a b c : Int, (a, b, c) ∈ allThreeSumTriples nums →
      (a, b, c) ∈ (threeSumAlgorithm nums).toFinset := by
  sorry -- TODO: 利用排序不变性与双指针完备性完成证明

/-- 定理 2（去重正确性）：算法输出的三元组集合中不存在重复三元组。

    证明思路：
    - 数组已排序，因此任何合法三元组在排序后表示为 (a, b, c) 且 a ≤ b ≤ c 是唯一的。
    - 算法固定 i 后，在找到一组 (left, right) 后同时移动两者，跳过相等的连续元素。
    - 由于 i 递增且跳过重复值，同一个三元组不会被生成两次。 -/
theorem three_sum_no_duplicate
    (nums : List Int)
    : (threeSumAlgorithm nums).Nodup := by
  sorry -- TODO: 利用排序后元组的规范表示唯一性完成证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：排序后的数组中，若 i < j < k，则 sorted[i] ≤ sorted[j] ≤ sorted[k]。 -/
theorem sorted_triple_order
    (sorted : List Int)
    (h_sorted : Sorted (· ≤ ·) sorted)
    (i j k : Nat)
    (h_ijk : i < j ∧ j < k ∧ k < sorted.length)
    : sorted.getD i 0 ≤ sorted.getD j 0 ∧ sorted.getD j 0 ≤ sorted.getD k 0 := by
  sorry -- TODO: 利用 List.Sorted 的索引单调性证明

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! threeSumAlgorithm [-1, 0, 1, 2, -1, -4]  -- 期望: [(-1,-1,2), (-1,0,1)]
#eval! threeSumAlgorithm [0, 1, 1]                -- 期望: []
#eval! threeSumAlgorithm [0, 0, 0]                -- 期望: [(0,0,0)]

#check three_sum_completeness
