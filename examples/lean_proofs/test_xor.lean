example (a : Nat) : a.xor a = 0 := by rfl
example (a : Nat) : a.xor 0 = a := by rfl
example (a b : Nat) : a.xor b = b.xor a := by rfl
example (a b c : Nat) : (a.xor b).xor c = a.xor (b.xor c) := by rfl
