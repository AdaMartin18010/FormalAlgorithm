example (o : Option Nat) (h : o ≠ none) : ∃ a, o = some a := by
  cases o with
  | none => contradiction
  | some a => exact ⟨a, rfl⟩
