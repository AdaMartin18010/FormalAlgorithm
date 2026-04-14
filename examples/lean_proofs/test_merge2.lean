def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

theorem test3 (x y : Nat) (ys : List Nat) (h : x ≤ y) : merge (x :: []) (y :: ys) = x :: y :: ys := by
  simp [merge, h]
