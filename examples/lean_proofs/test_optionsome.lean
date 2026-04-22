example (o : Option α) (h : o ≠ none) : o.isSome = true := by
  simp [Option.isSome_iff_exists]
  cases o with
  | none => contradiction
  | some a => exact ⟨a, rfl⟩
