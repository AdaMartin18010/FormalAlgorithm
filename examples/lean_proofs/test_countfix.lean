def countValue (xs : List Nat) (v : Nat) : Nat :=
  match xs with
  | [] => 0
  | x :: xs' => (if x = v then 1 else 0) + countValue xs' v

theorem countValue_replicate_zero (n : Nat)
    : countValue (List.replicate n 0) 0 = n := by
  induction n with
  | zero =>
    simp [countValue]
  | succ n ih =>
    simp [countValue, List.replicate, ih]
    <;> omega
