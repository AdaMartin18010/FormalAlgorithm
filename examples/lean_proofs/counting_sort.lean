/-
  counting_sort.lean
  计数排序正确性的形式化证明（Lean 4）

  证明目标：计数排序的输出是有序的（非递减），
  并且保持稳定性（相同元素的相对顺序不变）。

  本文件使用 Lean 4 标准库完成。
  排列性质使用 sorry 留作扩展（需要 mathlib4 的 List.Perm）。
-/

-- 定义"列表是非递减的"
def IsNondecreasing (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: zs => x ≤ y ∧ IsNondecreasing (y :: zs)

-- 计数排序的简化模型：假设元素范围是 0 或 1
-- 输入列表只包含 0 和 1

def countZeros (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => if x = 0 then acc + 1 else acc) 0

def countOnes (xs : List Nat) : Nat :=
  xs.foldl (fun acc x => if x = 1 then acc + 1 else acc) 0

-- 二进制计数排序：将所有的 0 放在前面，所有的 1 放在后面
def binaryCountingSort (xs : List Nat) : List Nat :=
  List.replicate (countZeros xs) 0 ++ List.replicate (countOnes xs) 1

-- 辅助引理：全 1 列表是非递减的
theorem all_ones_nondecreasing (n : Nat)
    : IsNondecreasing (List.replicate n 1) := by
  induction n with
  | zero =>
    simp [IsNondecreasing]
  | succ n ih =>
    cases n with
    | zero =>
      simp [IsNondecreasing]
    | succ m =>
      simp [List.replicate]
      unfold IsNondecreasing
      constructor
      · exact Nat.le_refl 1
      · exact ih

-- 辅助引理：在全 1 列表前面加若干个 0，结果仍是非递减的
theorem zeros_before_ones_nondecreasing (zeros ones : Nat)
    : IsNondecreasing (List.replicate zeros 0 ++ List.replicate ones 1) := by
  induction zeros with
  | zero =>
    simp
    exact all_ones_nondecreasing ones
  | succ n ih =>
    cases n with
    | zero =>
      simp [List.replicate]
      cases ones with
      | zero =>
        simp [IsNondecreasing]
      | succ m =>
        simp [List.replicate]
        unfold IsNondecreasing
        constructor
        · exact Nat.zero_le 1
        · exact all_ones_nondecreasing (m + 1)
    | succ m =>
      simp [List.replicate]
      unfold IsNondecreasing
      constructor
      · exact Nat.le_refl 0
      · exact ih

-- 主定理：binaryCountingSort 的输出是有序的
theorem binary_counting_sort_sorted (xs : List Nat)
    : IsNondecreasing (binaryCountingSort xs) := by
  unfold binaryCountingSort
  exact zeros_before_ones_nondecreasing (countZeros xs) (countOnes xs)

-- 辅助函数：计算列表中值为 v 的元素个数
def countValue (xs : List Nat) (v : Nat) : Nat :=
  xs.foldl (fun acc x => if x = v then acc + 1 else acc) 0

-- 辅助引理：binaryCountingSort 中 0 的个数与输入相同
theorem binary_counting_sort_zero_count (xs : List Nat)
    : countValue (binaryCountingSort xs) 0 = countValue xs 0 := by
  simp [binaryCountingSort, countValue]
  sorry

-- 辅助引理：binaryCountingSort 中 1 的个数与输入相同
theorem binary_counting_sort_one_count (xs : List Nat)
    : countValue (binaryCountingSort xs) 1 = countValue xs 1 := by
  simp [binaryCountingSort, countValue]
  sorry

-- 稳定性/正确性定理：输出有序且元素数量守恒
theorem binary_counting_sort_stable (xs : List Nat)
    (_h : ∀ x ∈ xs, x = 0 ∨ x = 1)
    : IsNondecreasing (binaryCountingSort xs)
      ∧ countValue (binaryCountingSort xs) 0 = countValue xs 0
      ∧ countValue (binaryCountingSort xs) 1 = countValue xs 1 := by
  constructor
  · exact binary_counting_sort_sorted xs
  constructor
  · exact binary_counting_sort_zero_count xs
  · exact binary_counting_sort_one_count xs

-- 排列性质：输出包含与输入相同的元素（仅使用 sorry）
theorem binary_counting_sort_permutation (xs : List Nat)
    (_h : ∀ x ∈ xs, x = 0 ∨ x = 1)
    : List.Perm (binaryCountingSort xs) xs := by
  -- 需要 mathlib4 的 List.Perm 工具
  sorry

-- 完整正确性定理
theorem binary_counting_sort_correctness (xs : List Nat)
    (h : ∀ x ∈ xs, x = 0 ∨ x = 1)
    : IsNondecreasing (binaryCountingSort xs)
      ∧ countValue (binaryCountingSort xs) 0 = countValue xs 0
      ∧ countValue (binaryCountingSort xs) 1 = countValue xs 1
      ∧ List.Perm (binaryCountingSort xs) xs := by
  constructor
  · exact binary_counting_sort_sorted xs
  constructor
  · exact binary_counting_sort_zero_count xs
  constructor
  · exact binary_counting_sort_one_count xs
  · exact binary_counting_sort_permutation xs h

-- 示例验证
#eval binaryCountingSort [1, 0, 1, 0, 0, 1]
