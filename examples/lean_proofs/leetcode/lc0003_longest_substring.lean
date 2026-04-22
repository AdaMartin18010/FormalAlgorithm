/-
  lc0003_longest_substring.lean
  LeetCode 3. 无重复字符的最长子串的形式化证明（Lean 4）

  证明目标：
    1. 定义字符串及子串的形式化模型。
    2. 实现滑动窗口算法：维护 window [left, right)，遇到重复字符时收缩 left。
    3. 证明核心不变式：窗口内始终无重复字符。
    4. 证明窗口收缩后仍保留找到最优解的可能性（即不遗漏更长子串）。

  依赖: Mathlib4 的列表、集合与字符串工具

  算法分析见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
  形式化方法见 docs/03-形式化证明/02-Hoare逻辑.md
-/

import Mathlib.Data.List.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Char.Basic

open List Char

-- ============================================================
-- 1. 问题实例的形式化定义
-- ============================================================

/-- 用字符列表表示字符串。 -/
abbrev MyString := List Char

/-- 子串定义：s[i..j]（含 i，不含 j）。 -/
def substring (s : MyString) (i j : Nat) : MyString :=
  (s.drop i).take (j - i)

/-- 子串无重复字符。 -/
def NoRepeats (s : MyString) : Prop :=
  s.Nodup

/-- 子串长度。 -/
def substrLength (s : MyString) (i j : Nat) : Nat :=
  j - i

/-- 最长无重复子串长度。 -/
def longestUniqueSubstring (s : MyString) : Nat :=
  let rec loop (left right best : Nat) (seen : Finset Char) : Nat :=
    if h : right < s.length then
      let c := s.get ⟨right, by omega⟩
      if c ∈ seen then
        let left' := left + 1
        let seen' := seen.erase (s.get ⟨left, by sorry⟩)
        loop left' right best seen'
      else
        let right' := right + 1
        let seen' := seen.insert c
        let best' := max best (right' - left)
        loop left right' best' seen'
    else
      best
  loop 0 0 0 ∅

-- 由于 Lean 的 partial def 限制，上面用递归定义。
-- 下面用更简单的纯函数定义来形式化。

/-- 滑动窗口函数的规范版本（非高效，但便于证明）。
    枚举所有满足无重复的子串，取最大长度。 -/
def longestUniqueSubstringSpec (s : MyString) : Nat :=
  let candidates := List.range (s.length + 1) |>.bind (fun i =>
    List.range' i (s.length + 1 - i) |>.filter (fun j =>
      NoRepeats (substring s i j)
    ) |>.map (fun j => j - i)
  )
  candidates.maximum?.getD 0

-- ============================================================
-- 2. 核心定理：滑动窗口正确性
-- ============================================================

/-- 引理（窗口不变式）：在滑动窗口算法的任意时刻，当前窗口 [left, right)
    内的子串无重复字符。

    证明思路：对 right 进行归纳。
    - 基础步：right = 0，窗口为空，显然无重复。
    - 归纳步：假设 [left, right) 无重复。处理 s[right] 时：
      - 若 s[right] 不在窗口中，窗口扩展为 [left, right+1)，仍无重复。
      - 若 s[right] 在窗口中，不断收缩 left 直到 s[right] 被移出，
        此时窗口仍无重复。 -/
theorem sliding_window_invariant
    (s : MyString) (left right : Nat)
    (h_left : left ≤ right)
    (h_right : right ≤ s.length)
    (h_inv : NoRepeats (substring s left right))
    : ∀ left' right',
      left ≤ left' ∧ left' ≤ right' ∧ right' ≤ right ∧
      NoRepeats (substring s left' right') →
      NoRepeats (substring s left right) := by
  sorry -- TODO: 利用 NoRepeats 的单调性完成证明

/-- 定理 1（不遗漏最优解）：当 right 端遇到重复字符并收缩 left 时，
    被收缩掉的左端字符不可能出现在任何以 right 结尾的更优子串中。

    形式化地：设 s[right] = c 且 c 在 [left, right) 中最左出现位置为 p，
    则任何以 right 结尾的无重复子串的左端点必 > p，因此将 left 收缩到 p+1
    不会遗漏更长的合法子串。

    证明思路：
    - 反证法：假设存在以 right 结尾的无重复子串 [l, right+1) 且 l ≤ p。
    - 则 s[p] = c 且 s[right] = c，且 p < right，因此 [l, right+1) 中有重复 c，矛盾。
    - 故 l 必 > p，left 可安全收缩到 p+1。 -/
theorem shrink_preserves_optimality
    (s : MyString) (left right p : Nat)
    (h_p : left ≤ p ∧ p < right)
    (h_char : s.get ⟨p, by sorry⟩ = s.get ⟨right, by sorry⟩)
    (h_leftmost : ∀ k, left ≤ k ∧ k < right ∧ s.get ⟨k, by sorry⟩ = s.get ⟨right, by sorry⟩ → p ≤ k)
    : ∀ l, left ≤ l ∧ l ≤ right ∧ NoRepeats (substring s l (right + 1)) → l > p := by
  sorry -- TODO: 反证法证明收缩左边界不会遗漏更优解

/-- 定理 2（滑动窗口最优性）：滑动窗口算法返回的长度等于最长无重复子串长度。

    证明思路：
    - 证明算法维护的 best 始终等于所有已遍历过的合法窗口的最大长度。
    - 由定理 1，每个以 right 结尾的最长合法窗口都会被考察到。
    - 遍历完所有 right 后，best 即为全局最长。 -/
theorem sliding_window_optimal
    (s : MyString)
    : longestUniqueSubstringSpec s =
      let rec loop (left right best : Nat) (seen : Finset Char) : Nat :=
        if h : right < s.length then
          let c := s.get ⟨right, by omega⟩
          if c ∈ seen then
            let left' := left + 1
            let seen' := seen.erase (s.get ⟨left, by sorry⟩)
            loop left' right best seen'
          else
            let right' := right + 1
            let seen' := seen.insert c
            let best' := max best (right' - left)
            loop left right' best' seen'
        else
          best
      loop 0 0 0 ∅ := by
  sorry -- TODO: 利用窗口不变式与不遗漏最优性定理完成证明

-- ============================================================
-- 3. 辅助引理
-- ============================================================

/-- 引理：子串的 NoRepeats 性质具有前缀保持性。
    若 s[i..j) 无重复，则对任意 k ∈ [i, j)，s[i..k) 也无重复。 -/
theorem nodup_prefix
    (s : MyString) (i j k : Nat)
    (h_ijk : i ≤ k ∧ k ≤ j)
    (h_nodup : NoRepeats (substring s i j))
    : NoRepeats (substring s i k) := by
  sorry -- TODO: 利用 List.Nodup 的前缀保持性证明

-- ============================================================
-- 4. 示例验证（非形式化测试）
-- ============================================================

#eval! longestUniqueSubstringSpec ['a', 'b', 'c', 'a', 'b', 'c', 'b', 'b']  -- 期望: 3 ("abc")
#eval! longestUniqueSubstringSpec ['b', 'b', 'b', 'b']                     -- 期望: 1 ("b")
#eval! longestUniqueSubstringSpec ['p', 'w', 'w', 'k', 'e', 'w']           -- 期望: 3 ("wke")
#eval! longestUniqueSubstringSpec ([] : MyString)                          -- 期望: 0

#check shrink_preserves_optimality
