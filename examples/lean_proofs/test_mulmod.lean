example (a n : Nat) : (a * n) % n = 0 := by
  rw [Nat.mul_mod]
  simp
