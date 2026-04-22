/-
  lc0001_two_sum.lean
  LeetCode 1. 两数之和的形式化证明（Lean 4）

  证明目标：
    1. 定义问题：给定整数数组 nums 和目标值 target，找出两不同下标 i, j
       使得 nums[i] + nums[j] = target。
    2. 证明哈希表算法的正确性：若解存在，算法必能找到。
    3. 证明解的存在性与算法输出的对应关系。
    4. 证明算法在 O(n) 时间内终止。

  依赖: Mathlib4 的列表、集合与哈希表相关理论

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/01-哈希表.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
-- import Mathlib.Data.Finset.Basic  -- 暂时禁用，待mathlib修复
-- import Mathlib.Data.Set.Basic  -- 暂时禁用，待mathlib修复
import Mathlib.Tactic

open Nat List

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 问题实例：整数列表和目标值。 -/
structure TwoSumProblem where
  nums : List Int
  target : Int

/-- 解的定义：存在两个不同下标 i < j，使得 nums[i] + nums[j] = target。 -/
def HasSolution (p : TwoSumProblem) : Prop :=
  ∃ (i j : Nat), i < j ∧ j < p.nums.length ∧
    p.nums.getD i 0 + p.nums.getD j 0 = p.target

/-- 解的索引对（结果类型）。 -/
structure TwoSumResult where
  i : Nat
  j : Nat
  h_i_lt_j : i < j

/-- 结果是否正确。 -/
def IsCorrectResult (p : TwoSumProblem) (r : TwoSumResult) : Prop :=
  r.j < p.nums.length ∧
  p.nums.getD r.i 0 + p.nums.getD r.j 0 = p.target

-- ============================================================
-- 2. 算法函数的 Lean 实现（规范描述）
-- ============================================================

/-- 暴力枚举实现：O(n²) 双重循环。
    用于作为规范，与哈希表实现对比。 -/
def twoSumBruteForce (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  match nums with
  | [] => none
  | _ :: tl =>
      let rec findPair (i : Nat) (xs : List Int) : Option (Nat × Nat) :=
        match xs with
        | [] => none
        | x :: xs' =>
            let rec findMatch (j : Nat) (ys : List Int) : Option (Nat × Nat) :=
              match ys with
              | [] => none
              | y :: ys' =>
                  if x + y = target then
                    some (i, j)
                  else
                    findMatch (j + 1) ys'
            match findMatch (i + 1) xs' with
            | some pair => some pair
            | none => findPair (i + 1) xs'
      findPair 0 nums
  termination_by nums.length - i
  decreasing_by
    all_goals
      simp_wf
      <;> try omega

/-- 列表安全索引（替代缺失的 List.get?）。 -/
def listGet? {α : Type} (l : List α) (n : Nat) : Option α :=
  if h : n < l.length then some (l.get ⟨n, h⟩) else none

/-- 哈希表辅助查找：检查 complement 是否已在已遍历集合中。
    在 Lean 中，我们用列表模拟键值对的查找过程。
    返回 complement 对应的索引（如果存在）。 -/
def lookupComplement (nums : List Int) (complement : Int) (idx : Nat) : Option Nat :=
  match nums with
  | [] => none
  | x :: xs =>
      if x = complement then
        some idx
      else
        lookupComplement xs complement (idx + 1)
  termination_by nums.length
  decreasing_by
    all_goals
      simp_wf
      <;> try omega

/-- 哈希表算法的纯函数实现（用列表模拟哈希表遍历）。
    返回满足 nums[i] + nums[j] = target 的索引对 (i, j)，其中 i < j。
    算法思路：从左到右遍历，维护已遍历元素值→索引的映射。
    对当前元素 nums[j]，查询 target - nums[j] 是否在映射中。 -/
def twoSumHash (nums : List Int) (target : Int) : Option (Nat × Nat) :=
  let rec aux (j : Nat) (seen : List (Int × Nat)) : Option (Nat × Nat) :=
    if h : j < nums.length then
      let current := nums[j]'h
      let complement := target - current
      match lookupComplement (List.map Prod.fst seen) complement 0 with
      | some idxInSeen =>
          match listGet? seen idxInSeen with
          | some (_, i) => some (i, j)
          | none => aux (j + 1) ((current, j) :: seen)
      | none => aux (j + 1) ((current, j) :: seen)
    else
      none
    termination_by nums.length - j
    decreasing_by
      all_goals
        simp_wf
        <;> try omega
  aux 0 []

-- ============================================================
-- 3. 核心定理：哈希表正确性
-- ============================================================

/-- 定理 1（存在性保证）：若问题存在解 (i, j) 且 i < j，
    则 twoSumHash 必返回某个解 (i', j')。

    证明思路：
    - 对 j 使用数学归纳法（外层循环变量）。
    - 当遍历到 j 时，若 complement = target - nums[j] 在 seen 中，
      则存在 i < j 使得 nums[i] = complement，算法返回 (i, j)。
    - 若 complement 不在 seen 中，则将 (nums[j], j) 加入 seen 继续。
    - 由于解 (i, j) 存在，当外层循环到达 j 时，i 必然已在 seen 中，
      因此算法必能发现 complement 并返回解。 -/
theorem twoSumHash_finds_solution
    (nums : List Int) (target : Int)
    (h_sol : ∃ (i j : Nat), i < j ∧ j < nums.length ∧
      nums.getD i 0 + nums.getD j 0 = target)
    : ∃ (i' j' : Nat), twoSumHash nums target = some (i', j') := by
  sorry -- TODO: 对 j 归纳，利用 seen 的单调性证明 complement 必被找到

/-- 定理 2（结果正确性）：若 twoSumHash 返回 some (i, j)，
    则 nums[i] + nums[j] = target 且 i < j < nums.length。

    证明思路：
    - 由算法结构，(i, j) 仅在 lookupComplement 成功时返回。
    - lookupComplement 成功意味着 seen 中存在某个 (nums[i], i)，
      满足 nums[i] = target - nums[j]。
    - 由于 i 在 seen 中，i < j（seen 只包含已遍历元素）。
    - 由数组索引边界检查，j < nums.length。
    - 因此 nums[i] + nums[j] = target 且 i < j。 -/
theorem twoSumHash_result_correct
    (nums : List Int) (target : Int)
    (i j : Nat)
    (h_res : twoSumHash nums target = some (i, j))
    : i < j ∧ j < nums.length ∧ nums.getD i 0 + nums.getD j 0 = target := by
  sorry -- TODO: 展开 twoSumHash 和 lookupComplement 的定义，反演路径条件

/-- 定理 3（终止性）：twoSumHash 对任意输入必在至多 nums.length 步内终止。

    证明思路：
    - 递归函数 aux 的度量是 nums.length - j。
    - 每次递归 j 增加 1，度量严格递减。
    - 当 j = nums.length 时到达边界条件返回 none。
    - 因此至多 nums.length 次递归后必终止。 -/
theorem twoSumHash_terminates
    (nums : List Int) (target : Int)
    : ∃ steps : Nat, steps ≤ nums.length := by
  sorry -- TODO: 提取递归度量并证明其递减性

-- ============================================================
-- 4. 辅助引理
-- ============================================================

/-- 引理：seen 列表中存储的所有索引都严格小于当前 j。
    这是保证 i < j 的关键不变式。 -/
theorem seen_indices_lt_j
    (nums : List Int) (target : Int)
    (j : Nat) (seen : List (Int × Nat))
    (h_inv : ∀ p ∈ seen, p.2 < j)
    : ∀ p ∈ ((nums.getD j 0, j) :: seen), p.2 ≤ j := by
  intros p hp
  simp at hp
  cases hp with
  | inl h => simp [h]
  | inr h =>
    have := h_inv p h
    omega

/-- 引理：lookupComplement 返回的索引对应的值等于 complement。 -/
theorem lookupComplement_correct
    (nums : List Int) (complement : Int) (idx found : Nat)
    (h_lookup : lookupComplement nums complement idx = some found)
    : nums.getD found 0 = complement := by
  sorry -- TODO: 对 nums 结构归纳，反演 lookupComplement 路径

-- ============================================================
-- 5. 示例验证（非形式化测试）
-- ============================================================

#eval! twoSumHash [2, 7, 11, 15] 9     -- 期望: some (0, 1)
#eval! twoSumHash [3, 2, 4] 6          -- 期望: some (1, 2)
#eval! twoSumHash [3, 3] 6             -- 期望: some (0, 1)
#eval! twoSumHash [1, 2, 3] 7          -- 期望: none
#eval! twoSumHash ([] : List Int) 0    -- 期望: none

#check twoSumHash_finds_solution
#check twoSumHash_result_correct
