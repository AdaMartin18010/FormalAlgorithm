def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

theorem test5 (x y : Nat) (ys : List Nat) (h : x ≤ y) :
  merge [] (y :: ys) = y :: ys := by
  simp [merge]
