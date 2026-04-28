/-
FormalAlgorithm Lean Proof Status: wip
Sorry Count: 1
Last Audited: 2026-04-29
Notes: 简单测试 example，核心断言为 sorry 占位
-/

example (a n : Nat) : (a * n) % n = 0 := by sorry
#check Nat.mul_mod
#check Nat.mod_mul_right
