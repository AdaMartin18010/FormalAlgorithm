-- Lean 4 自然数归纳证明示例
-- 对应 docs/03-形式化证明/05-证明助手实践.md
-- 注：Lean 4 标准库 Nat 已完整证明以下性质，此处展示如何调用及手写推导框架。

namespace NatInduction

open Nat

-- 定理：0 是加法的右单位元
-- 手写推导：n + 0 = n（对 n 归纳，zero 情形由定义得，succ 情形用 Nat.add_succ 展开）
theorem add_zero_right (n : Nat) : n + 0 = n :=
  Nat.add_zero n

-- 定理：后继的加法分配律
-- 手写推导：n + (m + 1) = (n + m) + 1（对 n 归纳，用 Nat.add_succ 展开）
theorem add_succ_right (n m : Nat) : n + (m + 1) = (n + m) + 1 :=
  Nat.add_succ n m

-- 定理：加法交换律
theorem add_comm (n m : Nat) : n + m = m + n :=
  Nat.add_comm n m

-- 定理：加法结合律
theorem add_assoc (n m p : Nat) : (n + m) + p = n + (m + p) :=
  Nat.add_assoc n m p

-- 教学注释：在 Lean 4 中，上述定理均已在 Init/Nat/Basic.lean 中通过结构归纳法严格证明。
-- 初学者可通过 `#print Nat.add_zero` 查看标准库的完整证明过程。

end NatInduction
