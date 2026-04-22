example (h : some x ≠ none) : (some x).isSome = true := by
  have : ∃ y, some x = some y := ⟨x, rfl⟩
  simp [Option.isSome_iff_exists, this]
