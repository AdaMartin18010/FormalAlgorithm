def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

theorem test1 (y : Nat) (ys : List Nat) : merge [] (y :: ys) = y :: ys := by
  simp [merge]

theorem test2 (x : Nat) (xs : List Nat) : merge (x :: xs) [] = x :: xs := by
  simp [merge]
