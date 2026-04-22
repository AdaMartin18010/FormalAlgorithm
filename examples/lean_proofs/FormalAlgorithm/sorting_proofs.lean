/-
  sorting_proofs.lean
  归并排序正确性的形式化证明（Lean 4）

  证明目标：归并排序的输出是有序的（非递减）。
  本文件主要使用 Lean 4 标准库完成，不涉及 mathlib4 的复杂定理。
  若需证明"输出是输入的一个排列"（完整正确性），则需要 mathlib4 中的
  List.Perm 等相关工具，留作后续扩展。
-/

-- 定义"列表是有序的"（非递减）
def IsSorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: zs => x ≤ y ∧ IsSorted (y :: zs)

-- 合并两个已排序的列表（标准归并）
def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

-- 归并排序。
-- 使用列表长度作为 well-founded 度量。
def mergeSort (xs : List Nat) : List Nat :=
  match xs with
  | [] => []
  | [x] => [x]
  | x :: y :: zs =>
    let n := (x :: y :: zs).length / 2
    merge (mergeSort ((x :: y :: zs).take n)) (mergeSort ((x :: y :: zs).drop n))
  termination_by xs.length
  decreasing_by
    simp_wf
    all_goals
      have _ : (x :: y :: zs).length ≥ 2 := by simp
      have _ : (x :: y :: zs).length / 2 < (x :: y :: zs).length := by
        apply Nat.div_lt_self
        · omega
        · decide
      try { omega }
      try { simp; omega }

-- 辅助引理：merge 保持有序性。
-- 使用外层对 xs 的归纳 + 内层对 ys 的归纳完成证明。
theorem merge_sorted (xs ys : List Nat)
    (h1 : IsSorted xs) (h2 : IsSorted ys)
    : IsSorted (merge xs ys) := by
  induction xs generalizing ys with
  | nil =>
    simp [merge]
    exact h2
  | cons x xs' ih_xs =>
    induction ys with
    | nil =>
      simp [merge]
      exact h1
    | cons y ys' ih_ys =>
      by_cases h_le : x ≤ y
      · -- x ≤ y 分支
        have eq : merge (x :: xs') (y :: ys') = x :: merge xs' (y :: ys') := by
          simp [merge, h_le]
        rw [eq]
        cases xs' with
        | nil =>
          simp [merge]
          unfold IsSorted
          exact ⟨h_le, h2⟩
        | cons x'' xs'' =>
          unfold IsSorted at h1
          cases h_merge : merge (x'' :: xs'') (y :: ys')
          · -- nil 分支：merge 永远不会返回 []，导出矛盾
            exfalso
            have contra : merge (x'' :: xs'') (y :: ys') ≠ [] := by
              intro h_eq
              simp [merge] at h_eq
              by_cases hc : x'' ≤ y
              · simp [hc] at h_eq
              · simp [hc] at h_eq
            rw [h_merge] at contra
            simp at contra
          · -- cons 分支
            rename_i a bs
            unfold IsSorted
            constructor
            · -- 证明 x ≤ a
              by_cases h3 : x'' ≤ y
              · simp [merge, h3] at h_merge
                rw [← h_merge.1]
                exact h1.1
              · simp [merge, h3] at h_merge
                rw [← h_merge.1]
                exact h_le
            · -- IsSorted (a :: bs)
              rw [← h_merge]
              apply ih_xs
              · exact h1.2
              · exact h2
      · -- x > y 分支
        have eq : merge (x :: xs') (y :: ys') = y :: merge (x :: xs') ys' := by
          simp [merge, h_le]
        rw [eq]
        cases ys' with
        | nil =>
          simp [merge]
          unfold IsSorted
          constructor
          · exact Nat.le_of_not_le h_le
          · exact h1
        | cons y'' ys'' =>
          unfold IsSorted at h2
          cases h_merge : merge (x :: xs') (y'' :: ys'')
          · -- nil 分支：merge 永远不会返回 []，导出矛盾
            exfalso
            have contra : merge (x :: xs') (y'' :: ys'') ≠ [] := by
              intro h_eq
              simp [merge] at h_eq
              by_cases hc : x ≤ y''
              · simp [hc] at h_eq
              · simp [hc] at h_eq
            rw [h_merge] at contra
            simp at contra
          · -- cons 分支
            rename_i a bs
            unfold IsSorted
            constructor
            · -- 证明 y ≤ a
              by_cases h3 : x ≤ y''
              · simp [merge, h3] at h_merge
                rw [← h_merge.1]
                exact Nat.le_of_not_le h_le
              · simp [merge, h3] at h_merge
                rw [← h_merge.1]
                exact h2.1
            · -- IsSorted (a :: bs)
              rw [← h_merge]
              apply ih_ys
              exact h2.2

-- 主定理：mergeSort 的输出是有序的。
-- 使用 mergeSort 的 well-founded 归纳原理完成证明。
theorem mergeSort_sorted (xs : List Nat)
    : IsSorted (mergeSort xs) := by
  induction xs using mergeSort.induct
  · simp [mergeSort, IsSorted]
  · simp [mergeSort, IsSorted]
  · rename_i x y zs n ih1 ih2
    simp [mergeSort]
    apply merge_sorted
    · exact ih1
    · exact ih2

-- 示例验证
#eval mergeSort [3, 1, 4, 1, 5, 9, 2, 6]
