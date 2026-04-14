def IsSorted (xs : List Nat) : Prop :=
  match xs with
  | [] => True
  | [_] => True
  | x :: y :: zs => x ≤ y ∧ IsSorted (y :: zs)

def merge (xs ys : List Nat) : List Nat :=
  match xs, ys with
  | [], _ => ys
  | _, [] => xs
  | x :: xs', y :: ys' =>
    if x ≤ y then x :: merge xs' (y :: ys')
    else y :: merge (x :: xs') ys'

theorem test4 (x y : Nat) (ys : List Nat) (h : x ≤ y) (h2 : IsSorted (y :: ys)) (h1 : IsSorted [x]) :
  IsSorted (merge [x] (y :: ys)) := by
  simp [IsSorted, merge]
  by_cases h' : x ≤ y
  · simp [h']
    cases ys with
    | nil =>
      simp [IsSorted, merge]
      exact And.intro h' h2
    | cons y' ys' =>
      simp [IsSorted, merge]
      sorry
  · simp [h']
    sorry
