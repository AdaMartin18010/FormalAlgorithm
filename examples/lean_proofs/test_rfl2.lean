def f (xs : List Nat) : Nat :=
  match xs with
  | [] => 0
  | _ :: xs' => 1 + f xs'

example : f ([] : List Nat) = ([] : List Nat).length := rfl
example (n : Nat) : 1 + n = n + 1 := by rw [Nat.add_comm]
