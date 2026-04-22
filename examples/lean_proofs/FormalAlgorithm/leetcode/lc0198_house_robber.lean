/-
  lc0198_house_robber.lean
  LeetCode 198. 打家劫舍问题的形式化证明（Lean 4）

  证明目标：
    1. 定义打家劫舍问题：相邻房屋不能同时偷窃，求最大金额。
    2. 证明最优子结构引理：最优解要么包含第 n 个元素，要么不包含。
    3. 若包含第 n 个，则第 n-1 个不能包含，问题归约为前 n-2 个房屋；
       若不包含第 n 个，问题归约为前 n-1 个房屋。

  依赖: Mathlib4 的列表与序理论

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Algebra.Order.Monoid.Defs

open Nat List

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 房屋金额列表。nums[i] 表示第 i 间房屋的金额。 -/
abbrev MoneyList := List Nat

/-- 合法偷窃方案：从列表中选取若干元素，使得任意两个被选元素在原列表中不相邻。
    返回值为（所选元素之和, 所选索引集合）。
    这里用索引列表表示选取方案，要求索引严格递增且相邻索引差不小于 2。 -/
def IsValidPlan (nums : MoneyList) (indices : List Nat) : Prop :=
  indices ⊆ List.range nums.length ∧
  indices.Sorted (· < ·) ∧
  (∀ i ∈ indices, ∀ j ∈ indices, i < j → j - i ≥ 2)

/-- 方案的总金额。 -/
def PlanValue (nums : MoneyList) (indices : List Nat) : Nat :=
  indices.foldl (fun acc i => acc + nums.getD i 0) 0

/-- 最优解：不存在其他合法方案的总金额更大。 -/
def IsOptimal (nums : MoneyList) (indices : List Nat) : Prop :=
  IsValidPlan nums indices ∧
  ∀ other : List Nat, IsValidPlan nums other → PlanValue nums other ≤ PlanValue nums indices

/-- 动态规划递推定义。
    dp[i] 表示前 i 间房屋（即 nums[0..i-1]）能获得的最大金额。 -/
def houseRobberDP (nums : MoneyList) : Nat → Nat
  | 0 => 0
  | 1 => nums.getD 0 0
  | n + 2 =>
      let robCurrent := nums.getD (n + 1) 0 + houseRobberDP nums n
      let skipCurrent := houseRobberDP nums (n + 1)
      max robCurrent skipCurrent

-- ============================================================
-- 2. 核心定理：最优子结构引理
-- ============================================================

/-- 定理 1（最优子结构）：设 nums 为金额列表，n = nums.length。
    对于前 n 间房屋的最优解，必有：
    - 要么最优解包含第 n-1 间房屋（最后一间），此时第 n-2 间不能包含，
      且前 n-2 间房屋的子方案必须是最优的；
    - 要么最优解不包含第 n-1 间房屋，此时前 n-1 间房屋的子方案必须是最优的。

    形式化地：dp[n] = max(nums[n-1] + dp[n-2], dp[n-1])。

    证明思路：
    - 对 n 使用数学归纳法。
    - 基础步 n = 0, 1  trivial。
    - 归纳步：假设对所有 k ≤ n+1 命题成立。
      考虑前 n+2 间房屋的任意最优解 S。
      若 S 包含第 n+1 间，则必不包含第 n 间，剩余部分为前 n 间的合法方案。
      若该剩余部分不是前 n 间的最优解，则可替换为更优方案，与 S 的最优性矛盾。
      若 S 不包含第 n+1 间，则 S 是前 n+1 间的合法方案，同理可证其必为前 n+1 间的最优解。 -/
theorem optimal_substructure
    (nums : MoneyList) (n : Nat)
    (h_n : n = nums.length)
    : houseRobberDP nums n =
      if n = 0 then 0
      else if n = 1 then nums.getD 0 0
      else max (nums.getD (n - 1) 0 + houseRobberDP nums (n - 2)) (houseRobberDP nums (n - 1)) := by
  sorry -- TODO: 对 n 使用归纳法，分情况讨论最优解是否包含最后一间房屋

/-- 定理 2（DP 最优性）：dp[n] 等于前 n 间房屋的最优偷窃金额。

    证明思路：
    - 利用定理 1 的最优子结构，通过归纳法证明 dp[n] 达到上界。
    - 对任意合法方案，其总金额不超过 dp[n]。 -/
theorem dp_is_optimal
    (nums : MoneyList) (n : Nat)
    (h_n : n ≤ nums.length)
    : ∀ indices : List Nat, IsValidPlan (nums.take n) indices →
      PlanValue (nums.take n) indices ≤ houseRobberDP nums n := by
  sorry -- TODO: 使用归纳法与最优子结构引理完成证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：若方案不包含相邻索引，则加入一个与已有索引都不相邻的新索引后，
    新方案仍不包含相邻索引。 -/
theorem valid_plan_extend
    (nums : MoneyList) (indices : List Nat) (i : Nat)
    (h_valid : IsValidPlan nums indices)
    (h_not_adj : ∀ j ∈ indices, |(i : Int) - j| ≥ 2)
    : IsValidPlan nums (i :: indices) := by
  sorry -- TODO: 验证索引范围、有序性和不相邻条件

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! houseRobberDP [1, 2, 3, 1] 4   -- 期望: 4  (偷 1 + 3)
#eval! houseRobberDP [2, 7, 9, 3, 1] 5 -- 期望: 12 (偷 2 + 9 + 1)
#eval! houseRobberDP [] 0               -- 期望: 0
#eval! houseRobberDP [5] 1              -- 期望: 5

#check optimal_substructure
