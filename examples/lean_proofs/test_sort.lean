def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

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
      have h : (x :: y :: zs).length ≥ 2 := by simp
      have h1 : (x :: y :: zs).length / 2 > 0 := by
        apply Nat.div_pos
        · omega
        · decide
      have h2 : (x :: y :: zs).length / 2 < (x :: y :: zs).length := by
        apply Nat.div_lt_self
        · omega
        · decide
      try { omega }
      try { simp [Nat.min_eq_left, Nat.le_of_lt, h2]; omega }
