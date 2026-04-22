/-
Minimal stub for Mathlib.Data.Nat.Fib.Basic
Provides the Fibonacci sequence definitions used in proofs.
-/

namespace Nat

/-- Fibonacci numbers: fib 0 = 0, fib 1 = 1, fib (n+2) = fib (n+1) + fib n -/
def fib : Nat → Nat
  | 0 => 0
  | 1 => 1
  | n + 2 => fib (n + 1) + fib n

/-- The defining recurrence relation for fib. -/
theorem fib_add_two (n : Nat) : fib (n + 2) = fib (n + 1) + fib n := by
  rfl

end Nat
