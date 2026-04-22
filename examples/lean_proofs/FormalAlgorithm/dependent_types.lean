/-
# 依赖类型示例 (Dependent Type Examples)

本文件展示 Lean 4 中的依赖类型构造：
- 依赖函数类型 (Π-type / Dependent function)
- 依赖对类型 (Σ-type / Dependent pair)
- 向量类型 (Vector，作为归纳族的典型示例)

依赖：仅需 Lean 4 核心库，无需额外 mathlib4。
-/

namespace DependentTypes

-- 1. 依赖函数类型 (Π-type) -------------------------------------------------

/-- 依赖恒等函数：类型为 Π (A : Type), A → A -/
def depId (A : Type) (a : A) : A := a

/-- 使用 `∀` 语法糖书写的依赖函数 -/
def swap {A B : Type} {C : A → B → Type}
    (f : (a : A) → (b : B) → C a b)
    (b : B) (a : A) : C a b :=
  f a b

-- 2. 依赖对类型 (Σ-type) --------------------------------------------------

/-- Σ 类型的构造：使用 Lean 核心库中的 `Sigma` -/
example (A : Type) (B : A → Type) (a : A) (b : B a)
    : (a : A) × (B a) :=
  ⟨a, b⟩

/-- Σ 类型的第一投影 -/
def sigmaFst {A : Type} {B : A → Type} (p : (a : A) × (B a)) : A :=
  p.1

/-- Σ 类型的第二投影，其类型依赖于第一分量的值 -/
def sigmaSnd {A : Type} {B : A → Type} (p : (a : A) × (B a)) : B p.1 :=
  p.2

-- 3. 向量类型 (Vector，归纳族) ---------------------------------------------

/-- 向量：长度索引化的列表类型 -/
inductive Vector (α : Type) : Nat → Type where
  | nil  : Vector α 0
  | cons : α → Vector α n → Vector α (n + 1)

open Vector

/-- 安全取头元素：类型保证向量非空 -/
def vhead {α : Type} {n : Nat} (v : Vector α (n + 1)) : α :=
  match v with
  | cons a _ => a

/-- 安全取尾：长度在类型中减 1 -/
def vtail {α : Type} {n : Nat} (v : Vector α (n + 1)) : Vector α n :=
  match v with
  | cons _ t => t

/-- 安全按索引取值：Fin n 保证索引在范围内 -/
def vnth {α : Type} {n : Nat} (v : Vector α n) (i : Fin n) : α :=
  match n, v, i with
  | _+1, cons a _,  ⟨0, _⟩    => a
  | _+1, cons _ t, ⟨i+1, h⟩ => vnth t ⟨i, by simp at h; exact h⟩

/-- 向量映射：保持长度不变 -/
def vmap {α β : Type} {n : Nat} (f : α → β) (v : Vector α n) : Vector β n :=
  match n, v with
  | 0,   nil        => nil
  | _+1, cons a t => cons (f a) (vmap f t)

/-- 证明：vmap 保持长度不变（由类型系统保证）且满足分配律 -/
example {α β γ : Type} {n : Nat} (f : β → γ) (g : α → β) (v : Vector α n)
    : vmap f (vmap g v) = vmap (fun x => f (g x)) v := by
  induction v with
  | nil => rfl
  | cons _ _ ih =>
    simp [vmap, ih]

end DependentTypes
