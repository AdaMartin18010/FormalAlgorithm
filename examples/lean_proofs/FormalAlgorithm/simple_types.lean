/-
# 简单类型论示例 (Simple Type Theory Examples)

本文件展示 Lean 4 中的简单类型构造：
- 函数类型 (Function / Arrow types)
- 积类型 (Product types)
- 和类型 (Sum types)

依赖：仅需 Lean 4 核心库，无需额外 mathlib4。
-/

namespace SimpleTypes

-- 1. 函数类型示例 ---------------------------------------------------------

/-- 函数复合：演示高阶函数类型 (β → γ) → (α → β) → (α → γ) -/
def compose {α β γ : Type} (f : β → γ) (g : α → β) : α → γ :=
  fun x => f (g x)

/-- 恒等函数：α → α -/
def idFun {α : Type} (x : α) : α := x

/-- 函数复合的结合律 -/
example {α β γ δ : Type} (f : γ → δ) (g : β → γ) (h : α → β)
    : compose f (compose g h) = compose (compose f g) h := by
  rfl

-- 2. 积类型示例 -----------------------------------------------------------

/-- 积类型的构造与投影：使用 Lean 核心库中的 `Prod` (记作 ×) -/
example (α β : Type) (a : α) (b : β) : α × β :=
  (a, b)

/-- 积类型的投影函数 -/
def proj₁ {α β : Type} (p : α × β) : α := p.1
def proj₂ {α β : Type} (p : α × β) : β := p.2

/-- 积类型的泛性质：给定 f : γ → α 和 g : γ → β，存在唯一的 ⟨f, g⟩ : γ → α × β -/
def pairMap {α β γ : Type} (f : γ → α) (g : γ → β) : γ → α × β :=
  fun c => (f c, g c)

-- 3. 和类型示例 -----------------------------------------------------------

/-- 和类型的构造：使用 Lean 核心库中的 `Sum` (记作 ⊕) -/
example (α β : Type) (a : α) : α ⊕ β :=
  Sum.inl a

example (α β : Type) (b : β) : α ⊕ β :=
  Sum.inr b

/-- 和类型的消去（case 分析）-/
def sumElim {α β γ : Type} (f : α → γ) (g : β → γ) : α ⊕ β → γ
  | Sum.inl a => f a
  | Sum.inr b => g b

/-- 和类型的注入是单射 -/
example {α β : Type} {a₁ a₂ : α} (h : (Sum.inl a₁ : α ⊕ β) = Sum.inl a₂)
    : a₁ = a₂ := by
  injection h

end SimpleTypes
