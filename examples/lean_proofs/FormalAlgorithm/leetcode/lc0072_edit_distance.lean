/-
FormalAlgorithm Lean Proof Status: partial
Sorry Count: 9
Last Audited: 2026-04-29
Notes: 非负性已证；边界正确性、最优子结构、同一性、对称性、三角不等式及终止性证明含 sorry 占位
-/

/-
  lc0072_edit_distance.lean
  LeetCode 72. 编辑距离的形式化证明（Lean 4）

  证明目标：
    1. 定义 Levenshtein 编辑距离：将字符串 word1 转换为 word2 的最少操作数。
    2. 操作包括：插入一个字符、删除一个字符、替换一个字符。
    3. 证明 DP 递推公式的正确性：双串归纳。
    4. 证明编辑距离满足度量空间公理（非负性、同一性、对称性、三角不等式）。

  依赖: Mathlib4 的字符串、列表与自然数工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

open Nat List

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 编辑操作类型：插入、删除、替换。 -/
inductive EditOp
  | insert (c : Char)
  | delete (c : Char)
  | substitute (c1 c2 : Char)
  deriving Repr

/-- 编辑距离 DP 的递归定义。
    editDistance xs ys 表示将列表 xs 转换为 ys 的最少操作数。
    对应 LeetCode 72 的标准 DP 递推：
    - dp[i][0] = i（删除 i 个字符）
    - dp[0][j] = j（插入 j 个字符）
    - 若 xs[i-1] = ys[j-1]，dp[i][j] = dp[i-1][j-1]
    - 否则 dp[i][j] = 1 + min(dp[i-1][j], dp[i][j-1], dp[i-1][j-1])
-/
def editDistance {α : Type} [BEq α] (xs ys : List α) : Nat :=
  match xs, ys with
  | [], [] => 0
  | [], _ :: ys' => 1 + editDistance [] ys'
  | _ :: xs', [] => 1 + editDistance xs' []
  | x :: xs', y :: ys' =>
      if x == y then
        editDistance xs' ys'
      else
        1 + min (min (editDistance xs' ys) (editDistance xs ys')) (editDistance xs' ys')
  termination_by xs.length + ys.length
  decreasing_by
    all_goals sorry

-- ============================================================
-- 2. 核心定理：DP 递推正确性
-- ============================================================

/-- 定理 1（边界正确性）：将空串转换为目标串的最少操作数为目标串长度。
    证明思路：只能逐个插入字符。 -/
theorem editDistance_empty_left {α : Type} [BEq α] (ys : List α)
    : editDistance [] ys = ys.length := by
  induction ys with
  | nil => simp [editDistance] <;> try rfl <;> sorry
  | cons y ys' ih =>
    simp [editDistance, ih]
    <;> try omega
    <;> try sorry

/-- 定理 2（边界正确性）：将源串转换为空串的最少操作数为源串长度。
    证明思路：只能逐个删除字符。 -/
theorem editDistance_empty_right {α : Type} [BEq α] (xs : List α)
    : editDistance xs [] = xs.length := by
  induction xs with
  | nil => simp [editDistance] <;> try rfl <;> sorry
  | cons x xs' ih =>
    simp [editDistance, ih]
    <;> try omega
    <;> try sorry

/-- 定理 3（最优子结构）：编辑距离满足最优子结构性质。
    对于非空串 x::xs' 和 y::ys'，若 x = y，则距离等于 editDistance xs' ys'；
    否则距离等于 1 加三种操作（删除/插入/替换）的最小值。

    证明思路（双串归纳）：
    - 基础：空串情况已由定理 1 和 2 覆盖。
    - 归纳：设 xs' 和 ys' 长度均小于当前串。
      若 x = y，则最优解的最后一步不需要操作这两个字符，
      问题归约为 xs' → ys'。
      若 x ≠ y，则最后一步必为三种操作之一：
      · 删除 x：代价 1 + editDistance xs' (y :: ys')
      · 插入 y：代价 1 + editDistance (x :: xs') ys'
      · 替换 x→y：代价 1 + editDistance xs' ys'
      取三者最小值即为最优。 -/
theorem editDistance_optimal_substructure {α : Type} [BEq α] (x y : α) (xs' ys' : List α)
    : editDistance (x :: xs') (y :: ys') =
      if x == y then
        editDistance xs' ys'
      else
        1 + min (min (editDistance xs' (y :: ys')) (editDistance (x :: xs') ys')) (editDistance xs' ys') := by
  sorry -- TODO: 展开 editDistance 定义，利用 if 分支完成等式证明

/-- 定理 4（非负性）：编辑距离总是非负整数。
    这是度量空间公理的一部分。 -/
theorem editDistance_nonneg {α : Type} [BEq α] (xs ys : List α)
    : editDistance xs ys ≥ 0 := by
  -- 由于 editDistance 返回 Nat，Nat 的所有值均 ≥ 0
  exact Nat.zero_le (editDistance xs ys)

/-- 定理 5（同一性）：编辑距离为 0 当且仅当两个串相等。
    注意：此定理在一般情况下对列表需要 decidable equality 的辅助。 -/
theorem editDistance_zero_iff_eq {α : Type} [BEq α] [LawfulBEq α] (xs ys : List α)
    : editDistance xs ys = 0 ↔ xs = ys := by
  sorry -- TODO: 对 xs 和 ys 的长度同时归纳，利用最优子结构证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：编辑距离满足对称性（在操作代价对称时）。
    证明思路：将插入与删除互换，替换双向等价。 -/
theorem editDistance_symmetric {α : Type} [BEq α] (xs ys : List α)
    : editDistance xs ys = editDistance ys xs := by
  sorry -- TODO: 对 xs.length + ys.length 使用强归纳法

/-- 引理：编辑距离满足三角不等式。
    editDistance xs zs ≤ editDistance xs ys + editDistance ys zs。 -/
theorem editDistance_triangle_inequality {α : Type} [BEq α] (xs ys zs : List α)
    : editDistance xs zs ≤ editDistance xs ys + editDistance ys zs := by
  sorry -- TODO: 构造复合编辑序列，利用最优性证明

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! editDistance ['h', 'o', 'r', 's', 'e'] ['r', 'o', 's']   -- 期望: 3 (horse → ros)
#eval! editDistance ['i', 'n', 't', 'e', 'n', 't', 'i', 'o', 'n']
                   ['e', 'x', 'e', 'c', 'u', 't', 'i', 'o', 'n'] -- 期望: 5
#eval! editDistance ([] : List Char) ([] : List Char)              -- 期望: 0
#eval! editDistance ['a'] ['a']                                    -- 期望: 0
#eval! editDistance ['a'] ['b']                                    -- 期望: 1
