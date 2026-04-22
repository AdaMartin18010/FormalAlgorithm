/-
  lc0053_maximum_subarray.lean
  LeetCode 53. 最大子数组和的形式化证明（Lean 4）

  证明目标：
    1. 定义最大子数组和问题。
    2. 实现 Kadane 算法（动态规划版本）。
    3. 证明 Kadane 算法的正确性：维护的局部最优值在遍历结束后即为全局最优。
    4. 证明“局部最优 → 全局最优”的归纳步骤。

  依赖: Mathlib4 的列表、整数序理论和有限集工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Algebra.Order.Ring.Int

open List Int

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 整数列表的子数组和：从索引 i 到 j（含）的元素之和。 -/
def subarraySum (nums : List Int) (i j : Nat) : Int :=
  (nums.drop i |>.take (j - i + 1)).foldl (· + ·) 0

/-- 最大子数组和：所有连续子数组和的最大值。
    若数组为空，定义为 0（或负无穷，此处按 LeetCode 惯例允许空子数组和为 0）。 -/
def maxSubarraySum (nums : List Int) : Int :=
  nums.foldl (fun (currentMax, globalMax) x =>
    let currentMax' := max x (currentMax + x)
    let globalMax' := max globalMax currentMax'
    (currentMax', globalMax')
  ) (0, 0) |>.snd

/-- 手工实现的 Kadane 算法递归版本，便于形式化证明。 -/
def kadane (nums : List Int) : Int × Int :=
  nums.foldl (fun (curr, best) x =>
    let curr' := max x (curr + x)
    let best' := max best curr'
    (curr', best')
  ) (0, 0)

/-- 提取 Kadane 算法的全局最优值。 -/
def maxSubarray (nums : List Int) : Int :=
  (kadane nums).snd

-- ============================================================
-- 2. 核心定理：Kadane 算法正确性
-- ============================================================

/-- 引理（局部最优不变式）：在第 i 步迭代时，curr 是以第 i-1 个元素结尾的
    所有子数组中的最大和。

    形式化地，设处理完前 i 个元素后的状态为 (curr_i, best_i)，则：
    - curr_i = max_{0 ≤ k ≤ i} (sum of nums[k..i-1])
    - best_i = max_{0 ≤ l ≤ r ≤ i} (sum of nums[l..r-1])

    证明思路：对 i 进行归纳。
    - 基础步 i=0：curr_0 = 0, best_0 = 0，空子数组的和为 0。
    - 归纳步：假设前 i 步成立。处理 nums[i] 时，
      curr_{i+1} = max(nums[i], curr_i + nums[i])。
      这恰好覆盖了"以 nums[i] 为起点的新子数组"和"延续前一个子数组"两种情况。
      best_{i+1} = max(best_i, curr_{i+1})，即全局最优要么不变，要么被 curr_{i+1} 更新。 -/
theorem kadane_local_optimal_invariant
    (nums : List Int) (i : Nat)
    (h_i : i ≤ nums.length)
    : let prefix := nums.take i
      let (curr, best) := kadane prefix
      curr = prefix.foldl (fun (curr' : Int) x => max x (curr' + x)) 0 := by
  sorry -- TODO: 使用 List.foldl 的性质与归纳法完成证明

/-- 定理 1（Kadane 全局最优性）：Kadane 算法返回的值等于所有连续子数组和的最大值。

    证明思路：
    - 利用局部最优不变式，证明 best_i 始终维护前 i 个元素的全局最优。
    - 遍历结束时 i = nums.length，best 即为全局最优。 -/
theorem kadane_global_optimal
    (nums : List Int)
    : maxSubarray nums =
      if nums.isEmpty then 0
      else
        let sums := List.range nums.length |>.bind (fun i =>
          List.range' i (nums.length - i) |>.map (fun j => subarraySum nums i j)
        )
        sums.maximum?.getD 0 := by
  sorry -- TODO: 利用局部最优不变式与全局最优的单调性完成证明

/-- 定理 2（局部最优 → 全局最优）：在每一步，curr 是以当前位置结尾的最大子数组和；
    全局最优 best 是所有 curr 值的最大值。因此遍历结束后 best 即为全局最优。

    这是 Kadane 算法正确性的核心洞察。 -/
theorem local_implies_global
    (nums : List Int)
    : ∀ i : Nat, i ≤ nums.length →
      let prefix := nums.take i
      let (_, best) := kadane prefix
      best = (List.range i |>.bind (fun l =>
        List.range' l (i - l) |>.map (fun r => subarraySum nums l r)
      )).maximum?.getD 0 := by
  sorry -- TODO: 使用归纳法证明全局最优的累积性质

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：subarraySum 满足可加性。
    subarraySum nums i k = subarraySum nums i j + subarraySum nums (j+1) k （当 i ≤ j ≤ k）。 -/
theorem subarraySum_append
    (nums : List Int) (i j k : Nat)
    (h_ijk : i ≤ j ∧ j ≤ k)
    : subarraySum nums i k = subarraySum nums i j + subarraySum nums (j + 1) k := by
  sorry -- TODO: 利用 drop 与 take 的分配律证明

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! maxSubarray [-2, 1, -3, 4, -1, 2, 1, -5, 4]  -- 期望: 6  ([4,-1,2,1])
#eval! maxSubarray [1]                               -- 期望: 1
#eval! maxSubarray [5, 4, -1, 7, 8]                  -- 期望: 23
#eval! maxSubarray ([] : List Int)                   -- 期望: 0

#check kadane_global_optimal
