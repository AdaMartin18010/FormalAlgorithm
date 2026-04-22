/-
  lc0070_climbing_stairs.lean
  LeetCode 70. 爬楼梯问题的形式化证明（Lean 4）

  证明目标：
    1. 定义爬楼梯问题：每次可爬 1 或 2 阶，求爬到第 n 阶的方法数。
    2. 证明 dp[n] = fib(n+1)，其中 fib(0)=0, fib(1)=1, fib(n)=fib(n-1)+fib(n-2)。
    3. 使用数学归纳法严格证明该等式对所有自然数 n 成立。

  依赖: Mathlib4 的自然数与数列工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.Nat.Fib.Basic
import Mathlib.Tactic

open Nat

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 爬楼梯的方法数递归定义。
    climbStairs n 表示爬到第 n 阶的不同方法总数。
    基准：爬到第 0 阶有 1 种方法（不动），第 1 阶有 1 种方法。
    递推：climbStairs n = climbStairs (n-1) + climbStairs (n-2)。
    对应 LeetCode 70 的 dp 定义。 -/
def climbStairs : Nat → Nat
  | 0 => 1
  | 1 => 1
  | n + 2 => climbStairs (n + 1) + climbStairs n

-- 标准斐波那契数列定义已从 Mathlib.Data.Nat.Fib.Basic 导入。

-- ============================================================
-- 2. 核心定理：dp[n] = fib(n+1)
-- ============================================================

/-- 定理 1（数学归纳法）：对任意自然数 n，爬楼梯的方法数等于 fib(n+1)。

    证明思路：
    - 基础步（n = 0）：climbStairs 0 = 1 = fib 1 = fib (0+1)。
    - 基础步（n = 1）：climbStairs 1 = 1 = fib 2 = fib (1+1)。
    - 归纳步：假设对所有 k ≤ n+1，climbStairs k = fib (k+1) 成立。
      则 climbStairs (n+2) = climbStairs (n+1) + climbStairs n
                           = fib (n+2) + fib (n+1)
                           = fib (n+3)
                           = fib ((n+2)+1)。
    - 由强归纳法原理，命题对所有自然数 n 成立。 -/
theorem climbStairs_eq_fib_succ (n : Nat) : climbStairs n = fib (n + 1) := by
  match n with
  | 0 =>
    simp [climbStairs, fib]
  | 1 =>
    simp [climbStairs, fib]
  | n + 2 =>
    -- 展开 climbStairs 递归定义
    rw [climbStairs]
    -- 应用归纳假设
    have ih1 := climbStairs_eq_fib_succ (n + 1)
    have ih2 := climbStairs_eq_fib_succ n
    rw [ih1, ih2]
    -- 利用 fib 递推关系：fib (n+3) = fib (n+2) + fib (n+1)
    simp [fib_add_two]
    <;> try omega

-- ============================================================
-- 3. 辅助引理：爬楼梯数列的基本性质
-- ============================================================

/-- 引理：climbStairs n > 0 对所有 n 成立。
    说明方法数总是正整数。 -/
theorem climbStairs_pos (n : Nat) : climbStairs n > 0 := by
  match n with
  | 0 => simp [climbStairs]
  | 1 => simp [climbStairs]
  | n + 2 =>
    rw [climbStairs]
    have h1 := climbStairs_pos (n + 1)
    have h2 := climbStairs_pos n
    omega

/-- 引理：climbStairs 满足与 fib 相同的递推关系。
    这是 climbStairs_eq_fib_succ 的直接推论。 -/
theorem climbStairs_recurrence (n : Nat) :
    climbStairs (n + 2) = climbStairs (n + 1) + climbStairs n := by
  simp [climbStairs]

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! climbStairs 2   -- 期望: 2  (1+1, 2)
#eval! climbStairs 3   -- 期望: 3  (1+1+1, 1+2, 2+1)
#eval! climbStairs 4   -- 期望: 5
#eval! climbStairs 10  -- 期望: 89

#check climbStairs_eq_fib_succ
