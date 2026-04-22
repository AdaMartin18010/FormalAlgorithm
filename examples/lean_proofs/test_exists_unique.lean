example (n : Nat) : ∃! m, m = n := by refine ⟨n, rfl, fun m h => h⟩
