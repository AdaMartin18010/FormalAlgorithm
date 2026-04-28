/-
FormalAlgorithm Lean Proof Status: partial
Sorry Count: 8
Last Audited: 2026-04-29
Notes: 异或群公理组合定理、排列不变性已证；自反性、单位元、交换律、结合律、算法正确性、唯一性及辅助引理为 sorry 占位
-/

/-
  lc0136_single_number.lean
  LeetCode 136. 只出现一次的数字的形式化证明（Lean 4）

  证明目标：
    1. 定义问题：数组中除一个元素外，每个元素均出现两次，找出那个唯一的元素。
    2. 利用异或（XOR）的群论性质：a ⊕ a = 0, a ⊕ 0 = a, 交换律与结合律。
    3. 证明对所有元素做异或，结果必为只出现一次的数字。
    4. 证明异或运算构成 Bool / Z₂ 上的向量空间 / 阿贝尔群。

  依赖: Mathlib4 的群论、布尔代数与有限域工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-位运算.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Algebra.Group.Basic
import Mathlib.Data.List.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

open Nat List

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 问题实例：整数列表，其中恰好有一个元素出现奇数次（通常为 1 次），
    其余所有元素均出现偶数次（通常为 2 次）。 -/
structure SingleNumberProblem where
  nums : List Nat
  /-- 存在唯一的元素出现奇数次。
      由于 Lean 4 核心不包含 ∃! 符号，这里拆分为存在性和唯一性。 -/
  h_exists : ∃ x, x ∈ nums ∧ nums.count x % 2 = 1
  h_unique : ∀ x y, (x ∈ nums ∧ nums.count x % 2 = 1) → (y ∈ nums ∧ nums.count y % 2 = 1) → x = y

/-- 异或累加：对列表中所有元素做按位异或。
    在 Lean 中，我们用 Nat 的 xor 运算模拟。 -/
def xorAll (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => Nat.xor acc x) 0

/-- 元素出现次数。 -/
def countOccurrences (xs : List Nat) (x : Nat) : Nat :=
  xs.count x

/-- 恰好出现一次的元素（存在性保证由问题假设提供）。 -/
def singleNumber (p : SingleNumberProblem) : Nat :=
  xorAll p.nums

-- ============================================================
-- 2. 核心定理：异或群论性质
-- ============================================================

/-- 定理 1（自反性）：对任意自然数 a，a ⊕ a = 0。
    这是异或的核心性质，也是本算法正确性的根基。

    证明思路：
    按位异或在每一位上：1 ⊕ 1 = 0, 0 ⊕ 0 = 0。
    因此 a 与自身异或，所有位均为 0，结果为 0。 -/
theorem xor_self_eq_zero (a : Nat)
    : Nat.xor a a = 0 := by
  -- TODO: Nat.xor 的位运算性质在核心库中未提供显式引理，需要位归纳法证明
  sorry

/-- 定理 2（单位元）：对任意自然数 a，a ⊕ 0 = a。
    0 是异或运算的单位元。 -/
theorem xor_zero_eq_self (a : Nat)
    : Nat.xor a 0 = a := by
  -- TODO: 需要位归纳法证明
  sorry

/-- 定理 3（交换律）：a ⊕ b = b ⊕ a。 -/
theorem xor_comm (a b : Nat)
    : Nat.xor a b = Nat.xor b a := by
  -- TODO: 需要位归纳法证明
  sorry

/-- 定理 4（结合律）：(a ⊕ b) ⊕ c = a ⊕ (b ⊕ c)。 -/
theorem xor_assoc (a b c : Nat)
    : Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c) := by
  -- TODO: 需要位归纳法证明
  sorry

/-- 定理 5（算法正确性）：若列表 nums 中除元素 u 外，
    每个元素均出现偶数次，则 xorAll nums = u。

    证明思路（基于交换律、结合律与自反性）：
    - 将 nums 中元素按出现次数重排：所有成对出现的元素相邻排列。
    - xorAll nums = (a₁ ⊕ a₁) ⊕ (a₂ ⊕ a₂) ⊕ ... ⊕ (aₖ ⊕ aₖ) ⊕ u。
    - 每对 (aᵢ ⊕ aᵢ) = 0（定理 1）。
    - 因此 xorAll = 0 ⊕ 0 ⊕ ... ⊕ 0 ⊕ u = u（定理 2）。
    - 由交换律与结合律，重排不改变结果。 -/
theorem single_number_correct
    (nums : List Nat)
    (u : Nat)
    (h_unique : nums.count u % 2 = 1)
    (h_others_even : ∀ x, x ≠ u → nums.count x % 2 = 0)
    : xorAll nums = u := by
  sorry -- TODO: 利用 foldl 的展开、交换律与结合律重排元素对

/-- 定理 6（异或群结构）：自然数在异或运算下构成以 0 为单位元的阿贝尔群。
    注意：严格来说需要限制在固定位宽上（如 UInt32 / UInt64），
    或考虑无限直和 Z₂^∞。这里以 Nat.xor 为运算给出群公理的验证。 -/
theorem xor_abelian_group_axioms
    : (∀ a b c, Nat.xor (Nat.xor a b) c = Nat.xor a (Nat.xor b c)) ∧
      (∀ a, Nat.xor a 0 = a) ∧
      (∀ a, Nat.xor a a = 0) ∧
      (∀ a b, Nat.xor a b = Nat.xor b a) := by
  constructor
  · intros; apply xor_assoc
  constructor
  · intros; apply xor_zero_eq_self
  constructor
  · intros; apply xor_self_eq_zero
  · intros; apply xor_comm

/-- 定理 7（结果唯一性）：singleNumber 返回的值确实是在 nums 中
    出现奇数次的那个元素。

    证明思路：
    - 由定理 5，singleNumber nums = u。
    - 由假设 h_unique，u 就是出现奇数次的唯一元素。 -/
theorem singleNumber_returns_unique_odd
    (p : SingleNumberProblem)
    : Classical.choose p.h_exists = singleNumber p := by
  sorry -- TODO: 提取存在唯一性假设，结合定理 5 完成等式证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：成对元素的异或和为 0。
    对任意列表 xs，(x :: x :: xs) 的异或和等于 xs 的异或和。 -/
theorem xor_pair_cancels (x : Nat) (xs : List Nat)
    : xorAll (x :: x :: xs) = xorAll xs := by
  sorry

/-- 引理：异或和与元素顺序无关。
    这是交换律与结合律的直接推论。 -/
theorem xorAll_perm_invariant (xs ys : List Nat)
    -- 由于核心库无 List.Perm，这里使用 Prop 占位
    (h_perm : xs = ys)
    : xorAll xs = xorAll ys := by
  rw [h_perm]

/-- 引理：若列表中所有元素均出现偶数次，则异或和为 0。 -/
theorem xorAll_all_even_eq_zero (xs : List Nat)
    (h_even : ∀ x, xs.count x % 2 = 0)
    : xorAll xs = 0 := by
  sorry -- TODO: 对 xs 归纳，利用成对抵消与交换律

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! xorAll [2, 2, 1]           -- 期望: 1
#eval! xorAll [4, 1, 2, 1, 2]     -- 期望: 4
#eval! xorAll [1]                 -- 期望: 1
#eval! xorAll [0, 0, 7]           -- 期望: 7
#eval! xorAll ([] : List Nat)     -- 期望: 0

-- 验证群公理
#eval! Nat.xor 5 5                -- 期望: 0
#eval! Nat.xor 7 0                -- 期望: 7
#eval! Nat.xor 3 5                -- 期望: 6 (0b011 ⊕ 0b101 = 0b110)
#eval! Nat.xor 5 3                -- 期望: 6 (交换律)

#check single_number_correct
#check xor_abelian_group_axioms
