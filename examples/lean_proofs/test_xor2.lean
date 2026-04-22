example (a : Nat) : a.xor a = 0 := by simp [Nat.xor]
example (a : Nat) : a.xor 0 = a := by simp [Nat.xor]
example (a b : Nat) : a.xor b = b.xor a := by simp [Nat.xor]
example (a b c : Nat) : (a.xor b).xor c = a.xor (b.xor c) := by simp [Nat.xor]
