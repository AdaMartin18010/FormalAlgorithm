#check Nat.max_le_max
example (a b c d : Nat) (h1 : a ≤ b) (h2 : c ≤ d) : max a c ≤ max b d := by
  apply Nat.max_le_max h1 h2
