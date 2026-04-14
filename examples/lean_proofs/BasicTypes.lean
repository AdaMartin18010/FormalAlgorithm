-- Lean 4 基础类型与函数示例
-- 对应 docs/03-形式化证明/05-证明助手实践.md

namespace BasicTypes

-- 1. 简单函数定义

def square (n : Nat) : Nat := n * n

def greet (name : String) : String := "Hello, " ++ name

-- 2. 多态函数 (Parametric Polymorphism)

def identity {α : Type} (x : α) : α := x

def compose {α β γ : Type} (f : β → γ) (g : α → β) (x : α) : γ := f (g x)

-- 3. 归纳数据类型：自定义列表

inductive MyList (α : Type) where
  | nil : MyList α
  | cons : α → MyList α → MyList α

deriving Repr

-- 4. 列表长度函数

def myLength {α : Type} : MyList α → Nat
  | MyList.nil => 0
  | MyList.cons _ t => 1 + myLength t

-- 5. 列表追加函数

def myAppend {α : Type} : MyList α → MyList α → MyList α
  | MyList.nil, ys => ys
  | MyList.cons x xs, ys => MyList.cons x (myAppend xs ys)

-- 6. 记录类型 (Structure)

structure Point where
  x : Float
  y : Float
  deriving Repr

def pointOrigin : Point := { x := 0.0, y := 0.0 }

def pointDistance (p q : Point) : Float :=
  Float.sqrt ((p.x - q.x) ^ 2.0 + (p.y - q.y) ^ 2.0)

-- 7. 依赖类型入门：定长向量

inductive Vect (α : Type) : Nat → Type where
  | nil : Vect α 0
  | cons : α → Vect α n → Vect α (n + 1)

deriving Repr

def vectHead {α : Type} {n : Nat} : Vect α (n + 1) → α
  | Vect.cons x _ => x

/-- 向量追加：使用 `Eq.symm (Nat.zero_add n)` 和 `Nat.succ_add` 处理类型索引。
    在 Lean 4 的依赖类型中，索引的相等性需要显式地用等式证明来转换。 -/
def vectAppend {α : Type} {m n : Nat} : Vect α m → Vect α n → Vect α (m + n)
  | Vect.nil, ys => Eq.symm (Nat.zero_add n) ▸ ys
  | Vect.cons x xs, ys => Nat.succ_add _ n ▸ Vect.cons x (vectAppend xs ys)

end BasicTypes
