/-
# HoTT 基础示例 (Homotopy Type Theory Basics)

本文件展示 Lean 4 中基于核心 `Eq` 类型的同伦类型论基础概念：
- 恒等类型 (Identity / Path type，即 `Eq`)
- 路径的对称性、传递性、连接 (symm, trans, cong)
- 运输 (transport) 与 依赖路径应用 (apd)

**注意**：
- Lean 4 核心库将 `Eq` 作为归纳族提供，具备基本的路径群胚结构。
- 完整的单值公理 (Univalence Axiom) 与 Higher Inductive Types (HITs)
  需要额外的 HoTT 库（如 `mathlib4` 中的相关部分或专门的 Cubical 扩展），
  不在核心库中直接提供。
- 以下代码仅依赖 Lean 4 核心库，展示可在标准 Lean 4 中直接运行的 HoTT 基础。
- 此处完整补全了 Mod2Rel 的等价关系证明。
-/

namespace HoTTBasics

universe u v

variable {A : Type u} {B : Type v}

-- 1. 恒等类型 (Id-type) 与基本路径操作 -------------------------------------

/-- 路径的对称性 (inverse) -/
def pathInv {x y : A} (p : x = y) : y = x :=
  Eq.symm p

/-- 路径的传递性 (concatenation) -/
def pathTrans {x y z : A} (p : x = y) (q : y = z) : x = z :=
  Eq.trans p q

/-- 路径上的函数作用 (ap / cong) -/
def pathAp (f : A → B) {x y : A} (p : x = y) : f x = f y :=
  congrArg f p

-- 2. 运输 (Transport) ------------------------------------------------------

/-- 沿路径在类型族中运输元素。
    对应 HoTT 中的 `transport^{P}(p, u) : P(y)`，其中 `p : x = y`，`u : P(x)`。 -/
def transport {P : A → Type u} {x y : A} (p : x = y) (u : P x) : P y :=
  p ▸ u

/-- 运输保持自反路径上的元素不变 -/
example {P : A → Type u} {x : A} (u : P x)
    : transport (rfl : x = x) u = u := by
  rfl

-- 3. 依赖路径应用 (apd) ----------------------------------------------------

/-- 对依赖函数 `f : (a : A) → P a` 应用路径 `p : x = y`，
    得到 `transport p (f x) = f y`。
    这对应 Rijke (2025) 中的 `apd` (dependent application of a path)。 -/
def apd {P : A → Type u} (f : (a : A) → P a) {x y : A} (p : x = y)
    : transport p (f x) = f y := by
  cases p
  rfl

-- 4. 基于 Quotient / Subtype 的等价概念 ----------------------------------

/-- 使用 `Subtype` 表达“某类型中满足给定性质的元素构成子类型”，
    这与 HoTT 中通过 Σ 类型构造子空间的思想一致。 -/
def EvenNat : Type := { n : Nat // n % 2 = 0 }

example : EvenNat := ⟨2, by decide⟩

/-- 使用 `Quotient` 表达通过等价关系对类型进行商化，
    这是 Lean 4 中构造“类型除以路径”的标准方式，
    与同伦类型论中通过 HITs 构造商类型的思想相通。 -/
inductive Mod2Rel : Nat → Nat → Prop where
  | intro (n m : Nat) (h : n % 2 = m % 2) : Mod2Rel n m

theorem Mod2Rel.refl (n : Nat) : Mod2Rel n n := by
  constructor
  rfl

theorem Mod2Rel.symm {n m : Nat} (h : Mod2Rel n m) : Mod2Rel m n := by
  cases h
  constructor
  rw [‹n % 2 = m % 2›]

theorem Mod2Rel.trans {n m k : Nat} (h1 : Mod2Rel n m) (h2 : Mod2Rel m k) : Mod2Rel n k := by
  cases h1
  cases h2
  rename_i h_nm h_mk
  constructor
  rw [h_nm, h_mk]

def Mod2 : Type :=
  @Quotient Nat (⟨Mod2Rel, Mod2Rel.refl, Mod2Rel.symm, Mod2Rel.trans⟩)
  -- 注：此处已完整证明等价关系的三条性质。

end HoTTBasics
