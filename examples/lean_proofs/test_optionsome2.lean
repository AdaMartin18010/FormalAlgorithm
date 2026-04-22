example (o : Option α) (h : o ≠ none) : o.isSome = true := by
  have : ∃ a, o = some a := by cases o <;> [contradiction; simp]
  simp [Option.isSome_iff_exists, this]
