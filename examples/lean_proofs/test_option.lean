example (h : some x ≠ none) : (some x).isSome = true := by simp
example (h : some x ≠ none) : ∃ y, some x = some y := by simp
