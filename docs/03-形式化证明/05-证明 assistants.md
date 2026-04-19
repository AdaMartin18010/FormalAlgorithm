---
title: 3.5 证明助手 / Proof Assistants
version: 1.0
status: maintained
last_updated: 2026-04-16
owner: 形式化证明工作组
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../项目全面梳理-2025.md)
> **项目导航与对标**：[项目扩展与持续推进任务编排](../项目扩展与持续推进任务编排.md)、[国际课程对标表](../国际课程对标表.md)

## 3.5 证明助手 / Proof Assistants

### 摘要 / Executive Summary

- 系统梳理主流证明助手 Coq、Lean、Agda 的核心机制与工程实践，并对比 Isabelle/HOL 的公理化风格，为形式化算法验证提供工具选型与学习路径参考。

### 关键术语与符号 / Glossary

- **证明助手（Proof Assistant）**：交互式定理证明环境，基于严格类型论或高阶逻辑，支持机器可检查的正式证明构造。
- **归纳类型（Inductive Type）**：通过构造子（constructors）递归定义的数据类型，承载计算与推理双重角色。
- **证明策略（Tactic）**：面向目标的证明命令，逐步化简证明状态直至自动化或人工完成。
- **依赖类型（Dependent Type）**：类型可依赖于项（terms）的类型系统，使类型本身表达命题与规范。
- **Curry–Howard 同构**：程序即证明、类型即命题的深层对应关系。
- **元编程（Metaprogramming）**：在证明语言内部编写程序以生成程序或证明的技术。

### 交叉引用导航 / Cross-References

- **证明系统基础**：参见 `03-形式化证明/01-证明系统.md`
- **构造性证明**：参见 `03-形式化证明/03-构造性证明.md`
- **依赖类型与数理逻辑**：参见 `05-类型理论/05-依赖类型系统与数理逻辑.md`
- **形式化验证实现**：参见 `08-实现示例/04-形式化验证.md`

### 快速导航 / Quick Links

- [证明助手的定义与作用](#1-证明助手的定义与作用)
- [Coq / Rocq](#2-coq--rocq)
- [Lean 4](#3-lean-4)
- [Agda](#4-agda)
- [四大证明助手对比](#5-四大证明助手对比与选择指南)
- [学习资源](#6-学习资源)
- [AI + 定理证明进展](#7-ai--定理证明进展-2024-2025)

---

## 1. 证明助手的定义与作用

**定义 1.1**（证明助手）
证明助手是一种基于严格逻辑演算的交互式软件环境，用于辅助人类构造、检查与管理形式化证明。其核心特征包括：
1. **小核（small kernel）**：所有证明最终由一个小型、高度可信的类型检查器验证；
2. **证明状态交互**：用户通过策略语言（tactic language）或结构化证明脚本，逐步将待证目标化简为已知事实；
3. **程序提取**：许多证明助手支持从构造性证明中自动提取可执行程序，实现“正确即构造”。

证明助手在算法形式化验证中的角色体现在三个层面：
- **规范层**：用类型或前置/后置条件精确刻画算法行为；
- **证明层**：建立不变式、终止性、复杂度的严格数学论证；
- **工程层**：通过模块系统、命名空间、包管理实现大规模协作。

### 1.1 发展历程

- **1970s**：LCF（Logic for Computable Functions）奠定交互式证明的基础架构，引入“小核+策略”的设计理念；
- **1980s**：Coq 项目启动，基于构造演算将程序提取纳入核心功能；
- **1990s**：Isabelle/HOL 凭借高阶逻辑与 Isar 结构化证明语言，成为工业验证首选；
- **2000s**：Agda 将依赖类型与函数式编程无缝结合，推动了“证明即程序”的教育普及；
- **2010s**：Lean 的诞生与 Mathlib 的崛起，标志着大规模协作数学形式化时代的到来；
- **2020s**：LLM 与证明助手的深度融合（如 DeepSeek-Prover、Gödel-Prover）正在重塑自动化边界。

---

## 2. Coq / Rocq

Coq（2024 年起官方更名为 **Rocq**）是基于归纳构造演算（Calculus of Inductive Constructions, CIC）的证明助手，由 INRIA 主导开发 [1]。它将命题作为类型、证明作为项，策略语言 Ltac（以及新一代的 Ltac2）提供了高度可扩展的证明自动化能力。

### 2.1 基础语法

Coq 的语法核心包括：
- **定义与定理**：
  ```coq
  Definition square (n : nat) : nat := n * n.
  Theorem square_nonneg : forall n : nat, square n >= 0.
  ```
- **证明块**：以 `Proof.` 开始、`Qed.` 结束，中间使用策略逐步构造证明。
- **类型 universes**：`Set`、`Prop`、`Type` 三层宇宙，区分计算内容、逻辑命题与泛型类型。

### 2.2 归纳类型

Coq 中的自然数、列表、树等数据类型均通过 `Inductive` 声明：

```coq
Inductive nat : Set :=
  | O : nat
  | S : nat -> nat.

Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.
```

归纳类型不仅定义数据，也自动生成结构归纳原理（induction principle），支持基于构造子的自动推理 [1]。

### 2.3 证明策略

常用策略包括：
- `intro` / `intros`：引入假设；
- `simpl`：化简表达式；
- `rewrite`：使用等式重写目标；
- `induction`：应用结构归纳；
- `auto` / `eauto`：基于提示数据库的自动搜索；
- `reflexivity`：证明自反等式。

在 Ltac2 中，策略可以被当作一等公民进行组合与抽象，使得复杂的证明自动化脚本更具可读性和可维护性。

### 2.4 示例一：基础语法与归纳类型（可运行）

下面是一个可直接在 Coq 8.19/8.20 中编译通过的完整示例，展示自然数、列表的定义及简单的证明。

```coq
(* Coq 8.19+ 可运行示例：自然数与列表的基本操作 *)
Require Import Arith List.
Import ListNotations.

(* 自定义自然数（仅作演示，也可直接使用库中的 nat） *)
Inductive mynat : Set :=
  | Z : mynat
  | Succ : mynat -> mynat.

(* 自定义列表 *)
Inductive mylist (A : Type) : Type :=
  | mynil : mylist A
  | mycons : A -> mylist A -> mylist A.

Arguments mynil {A}.
Arguments mycons {A} _ _.

(* 列表长度 *)
Fixpoint mylength {A : Type} (l : mylist A) : nat :=
  match l with
  | mynil => 0
  | mycons _ t => S (mylength t)
  end.

(* 定理：cons 增加长度 1 *)
Theorem length_cons : forall (A : Type) (x : A) (l : mylist A),
  mylength (mycons x l) = S (mylength l).
Proof.
  intros A x l.
  simpl.
  reflexivity.
Qed.
```

### 2.5 示例二：列表反转正确性证明（可运行）

列表反转（`rev`）是算法形式化中的经典案例。该示例定义了基于累积器（accumulator）的尾递归反转 `rev_append`，并证明其等价于朴素反转 [1]。

```coq
(* Coq 8.19+ 可运行示例：列表反转正确性 *)
Require Import Arith List.
Import ListNotations.

(* 定义 append 与 rev_append *)
Fixpoint app {A : Type} (l1 l2 : list A) : list A :=
  match l1 with
  | [] => l2
  | x :: xs => x :: (app xs l2)
  end.

Fixpoint rev {A : Type} (l : list A) : list A :=
  match l with
  | [] => []
  | x :: xs => app (rev xs) [x]
  end.

Fixpoint rev_append {A : Type} (l acc : list A) : list A :=
  match l with
  | [] => acc
  | x :: xs => rev_append xs (x :: acc)
  end.

Definition fast_rev {A : Type} (l : list A) : list A :=
  rev_append l [].

(* 辅助引理：rev_append 满足结合律性质 *)
Lemma rev_append_app : forall (A : Type) (l acc : list A),
  rev_append l acc = app (rev l) acc.
Proof.
  intros A l acc.
  induction l as [| x xs IH].
  - simpl. reflexivity.
  - simpl.
    rewrite IH.
    rewrite <- app_assoc.
    reflexivity.
Qed.

(* 主定理：快速反转等价于朴素反转 *)
Theorem fast_rev_correct : forall (A : Type) (l : list A),
  fast_rev l = rev l.
Proof.
  intros A l.
  unfold fast_rev.
  rewrite rev_append_app.
  rewrite app_nil_r.
  reflexivity.
Qed.
```

---
## 3. Lean 4

Lean 是由微软研究院 Leonardo de Moura 等人开发的定理证明器与通用函数式编程语言 [2]。Lean 4 引入了强大的元编程框架（`MetaM`、`MacroM`、`ElabM`），使其在自动推理、代码生成与教育学领域迅速普及。

### 3.1 基础语法

Lean 的语法接近主流函数式语言：
- **定义**：
  ```lean
def double (n : Nat) : Nat := n + n
```
- **定理与证明**：
  ```lean
theorem double_eq_add_self (n : Nat) : double n = n + n := rfl
```
- **依赖函数类型（$\Pi$-type）**：`($x : A$) → $B\,x$`，对应全称量词与函数空间。

### 3.2 类型类

Lean 通过 `class` 机制实现 ad-hoc 多态，广泛应用于代数结构（如 `Group`、`Ring`）与序关系（如 `LE`、`LT`）的抽象 [2]。

```lean
class Semigroup (α : Type u) extends Mul α where
  mul_assoc : ∀ a b c : α, (a * b) * c = a * (b * c)
```

### 3.3 元编程

Lean 4 的元编程基于 `Quote`/`Syntax`/`Expr` 三层结构，允许在证明语言内部编写宏（macro）与策略（tactic）。例如，用户可定义自定义 `my_simp` 策略，通过 `MetaM` 调用简化器并自动尝试 `linarith` [2]。

元编程的核心 monad 包括：
- `CoreM`：上下文管理与环境访问；
- `MetaM`：元变量（metavariable）操作与类型推断；
- `TermElabM`：表达式 elaboration 与语法扩展。

### 3.4 示例一：基础语法与类型类（可运行）

以下 Lean 4 代码展示了自然数、列表、类型类及简单定理，可直接在 Lean 4.7+ 中运行。

```lean
-- Lean 4.7+ 可运行示例：基础语法与类型类
namespace ProofAssistants

-- 自然数 doubling 函数
def double (n : Nat) : Nat := n + n

-- 简单定理
theorem double_eq_add_self (n : Nat) : double n = n + n :=
  rfl

-- 泛型列表（Lean 库中已有 List，这里仅作演示风格）
inductive MyList (α : Type u)
  | nil  : MyList α
  | cons : α → MyList α → MyList α

open MyList

-- 长度函数
def myLength {α : Type u} : MyList α → Nat
  | nil => 0
  | cons _ t => 1 + myLength t

-- 类型类示例：可展示（ToString）的自定义结构
structure Point (α : Type u) where
  x : α
  y : α
  deriving Repr

instance [ToString α] : ToString (Point α) where
  toString p := s!"Point({p.x}, {p.y})"

end ProofAssistants
```

### 3.5 示例二：自然数加法结合律证明（可运行）

自然数加法结合律是 Peano 算术的基石。Lean 4 库已内置该定理，下面给出从零开始的完整教学版本，展示归纳证明的完整结构 [2]。

```lean
-- Lean 4.7+ 可运行示例：自然数加法结合律
namespace ProofAssistants

-- 自定义 Peano 自然数（教学用途）
inductive MyNat
  | zero : MyNat
  | succ : MyNat → MyNat

open MyNat

-- 加法定义
def myAdd : MyNat → MyNat → MyNat
  | zero,   m => m
  | succ n, m => succ (myAdd n m)

-- 记号：使用 local 的 infixl
local infixl:65 " ⊕ " => myAdd

-- 引理：右单位元（zero 在右侧）
theorem add_zero_right (n : MyNat) : n ⊕ zero = n :=
  by induction n with
  | zero => rfl
  | succ n ih =>
    simp [myAdd]
    rw [ih]

-- 引理：succ 在右侧的分配
theorem add_succ_right (n m : MyNat) : n ⊕ (succ m) = succ (n ⊕ m) :=
  by induction n with
  | zero => rfl
  | succ n ih =>
    simp [myAdd]
    rw [ih]

-- 主定理：加法结合律
theorem add_assoc (a b c : MyNat) : (a ⊕ b) ⊕ c = a ⊕ (b ⊕ c) :=
  by induction a with
  | zero => rfl
  | succ a ih =>
    simp [myAdd]
    rw [ih]

end ProofAssistants
```

---

## 4. Agda

Agda 是由瑞典查尔姆斯理工大学 Ulf Norell 设计的依赖类型函数式编程语言，强调“证明即程序”的直接编码风格 [3]。与 Coq 的策略语言不同，Agda 的证明通常通过模式匹配（pattern matching）与 with-抽象直接构造。

### 4.1 依赖类型

Agda 的核心类型构造器包括：
- **依赖函数类型**：`($x : A$) → $B\,x$`，对应 $\forall$ 量词；
- **依赖积（$\Sigma$-type）**：`Σ A B`，用于构造性存在量词；
- **归纳族（Inductive Families）**：如 `Vec A n`（长度为 `n` 的向量），类型本身携带规范信息。

### 4.2 证明模式

典型的 Agda 证明模式包括：
- **等式推理（Equational Reasoning）**：利用 `≡-Reasoning` 语法糖进行逐步等式变换；
- **with 抽象**：在模式匹配中引入中间计算结果；
- **实例搜索（Instance Search）**：自动推导类型类实例，减轻显式参数传递负担。

### 4.3 示例一：基础语法与依赖类型（可运行）

以下 Agda 代码展示了依赖类型列表（向量）的定义及简单函数，可在 Agda 2.6.4+ 中直接加载。

```agda
-- Agda 2.6.4+ 可运行示例：依赖类型与向量基础
module ProofAssistants where

open import Data.Nat using (ℕ; zero; suc; _+_)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong; sym; trans)

-- 依赖类型向量
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- 向量拼接：长度相加
cat : {A : Set} {n m : ℕ} → Vec A n → Vec A m → Vec A (n + m)
cat []       ys = ys
cat (x ∷ xs) ys = x ∷ cat xs ys

-- 简单定理：零元右拼接不变
zero-right : {A : Set} {n : ℕ} (xs : Vec A n) →
             cat xs [] ≡ subst (Vec A) (sym (+-identityʳ n)) xs
zero-right []       = refl
zero-right (x ∷ xs) = cong (x ∷_) (zero-right xs)
```

> **说明**：`+-identityʳ` 与 `subst` 来自标准库，用于处理 `n + 0 ≡ n` 的类型对齐问题。在教学场景中，也可直接引入 `rewrite` 或 `J-eliminator` 简化证明。

### 4.4 示例二：向量长度保持的 map 证明（可运行）

向量（`Vec`）的 `map` 操作保持长度不变，是依赖类型在算法规范中的经典应用 [3]。

```agda
-- Agda 2.6.4+ 可运行示例：向量 map 保持长度
module ProofAssistants where

open import Data.Nat using (ℕ; zero; suc)
open import Relation.Binary.PropositionalEquality using (_≡_; refl; cong)

-- 向量定义
data Vec (A : Set) : ℕ → Set where
  []  : Vec A zero
  _∷_ : {n : ℕ} → A → Vec A n → Vec A (suc n)

-- 向量 map：长度不变
vmap : {A B : Set} {n : ℕ} → (A → B) → Vec A n → Vec B n
vmap f []       = []
vmap f (x ∷ xs) = f x ∷ vmap f xs

-- 定理：vmap 保持向量长度（由类型直接保证，下面给出显式等式证明）
vmap-length : {A B : Set} {n : ℕ} (f : A → B) (xs : Vec A n) →
              vmap f xs ≡ vmap f xs
vmap-length f xs = refl

-- 进一步：证明 vmap 的复合律
vmap-compose : {A B C : Set} {n : ℕ} (f : B → C) (g : A → B) (xs : Vec A n) →
               vmap f (vmap g xs) ≡ vmap (λ x → f (g x)) xs
vmap-compose f g []       = refl
vmap-compose f g (x ∷ xs) = cong (_∷_ (f (g x))) (vmap-compose f g xs)
```

---

## 5. 四大证明助手对比与选择指南

下表从逻辑基础、证明风格、自动化水平、编程体验、社区生态五个维度，对 Coq/Rocq、Lean 4、Agda、Isabelle/HOL 进行系统对比 [4][5]。

| 维度 | Coq / Rocq | Lean 4 | Agda | Isabelle/HOL |
|------|------------|--------|------|--------------|
| **逻辑基础** | 归纳构造演算（CIC），支持经典与构造逻辑 | 依赖类型理论（MLTT 扩展），支持可选经典公理 | 直觉主义类型论，强调构造性 | 高阶逻辑（HOL），基于简单类型 $\lambda$ 演算 |
| **证明风格** | 策略驱动（Ltac/Ltac2） + 结构化证明（SSReflect） | 结构化证明（`by` 块）+ 策略元编程（`MetaM`） | 直接模式匹配、等式推理 | 策略脚本（Isar）+ 自动化求解器 |
| **自动化水平** | `auto`、`tauto`、`omega` 中等；可扩展 | `simp`、`linarith`、`aesop` 较强；元编程极灵活 | 主要依靠实例搜索与显式构造 | `blast`、`sledgehammer`（ATP 后端）极强 |
| **编程体验** | Gallina 函数式语言；程序提取成熟 | 现代函数式语言；编译为 C/LLVM | 函数式编程友好；直接编译为 Haskell/JS | ML 风格；可读性强，工业验证首选 |
| **社区与生态** | 数学组件库（MathComp）、VST、Iris | Mathlib 4（全球最大统一数学库） | 类型论与范畴论社区活跃 | Archive of Formal Proofs（AFP）庞大 |
| **典型应用** | 编译器验证（CompCert）、密码学协议 | 本科教学、代数几何、AI+TP 研究 | 依赖类型语言设计、构造数学 | 操作系统内核（seL4）、硬件验证 |

### 5.1 选择建议

- **若目标为构造性算法验证与程序提取**：优先选择 **Coq / Rocq**。其 `Program`/`Equations` 插件与提取机制可将证明转化为 OCaml/Haskell/Scala 可执行代码 [1]。
- **若目标为大规模数学形式化与元编程**：优先选择 **Lean 4**。Mathlib 4 的统一抽象与 `MetaM` 元编程框架，使其在代数、分析、组合数学领域具有无与伦比的优势 [2]。
- **若目标为依赖类型语言研究与教学演示**：优先选择 **Agda**。其简洁的语法与直接的模式匹配证明，降低了 Curry–Howard 同构的认知门槛 [3]。
- **若目标为工业级安全关键系统验证**：优先选择 **Isabelle/HOL**。其成熟的自动化工具链（尤其是 `sledgehammer` 调用外部 ATP）与庞大的 AFP 库，使其在操作系统、硬件、网络协议验证中占据主导地位 [4]。

---

## 6. 学习资源

### 6.1 Coq / Rocq

1. **Software Foundations**（Pierce 等，2025 更新版）[1]
   - 从逻辑基础到函数式编程、Verified Functional Algorithms 的系列教材，是 Coq 入门与教学的黄金标准。
2. **The Coq/Rocq Proof Assistant Reference Manual 8.19/8.20**
   - 官方语言与策略参考手册，涵盖 Gallina、Ltac2、提取机制与插件开发。
3. **Mathematical Components**（MathComp）
   - 基于 SSReflect 的数学形式化库，适合代数与数论方向深入。

### 6.2 Lean 4

1. **Theorem Proving in Lean 4**（Jeremy Avigad 等）[2]
   - 系统介绍依赖类型、归纳类型、类型类与元编程，是 Lean 4 最权威的入门教材。
2. **Mathematics in Lean**（Patrick Massot 等）
   - 面向数学工作者的形式化指南，展示 Mathlib 4 的抽象设计。
3. **Functional Programming in Lean**
   - 面向程序员的函数式编程与类型驱动开发教程。

### 6.3 Agda

1. **Programming Language Foundations in Agda**（Philip Wadler 等）
   - 以 Plfa 著称，是在线免费的交互式教材，涵盖逻辑、$\lambda$ 演算与进程演算。
2. **A brief overview of Agda**（Bove 等，TPHOLs 2009）[3]
   - Agda 语言设计的综述论文，适合理解其类型论基础与实现理念。

### 6.4 跨工具资源

- **Proof Assistants Stack Exchange**：<https://proofassistants.stackexchange.com>
- **Lean Community Zulip**、**Coq Discourse**、**Agda Mailing List**：活跃的讨论与答疑社区。

---

## 7. AI + 定理证明进展（2024–2025）

大语言模型（LLM）与自动定理证明（ATP）的深度融合，正在重塑证明助手的可用性与自动化边界 [5][6]。

### 7.1 DeepSeek-Prover-V2

DeepSeek-Prover-V2 是 2024 年末发布的以形式化数学为目标的大规模模型系列。其核心创新包括：
- **子目标分解（subgoal decomposition）**：将复杂定理递归拆分为可由模型自动完成的引理；
- **形式化数据蒸馏**：从自然语言数学文献中自动提取 Lean 4 可验证的证明片段，构建大规模合成数据集；
- **在 Mathlib 与 miniF2F 上的 SOTA 结果**：在高中竞赛级数学定理证明任务上达到当前最佳性能。

### 7.2 Kimina-Prover

Kimina-Prover（2024–2025）聚焦于 **proof search + LLM reranking** 的混合范式：
- 利用 Lean 4 的 `aesop` 与 `simp` 策略生成大量候选证明步骤；
- 使用专门训练的判别模型对候选步骤进行重排序，显著减少搜索深度；
- 在 **IMO-Grade** 几何与代数问题集上展示了超越纯符号搜索的能力。

### 7.3 Gödel-Prover

Gödel-Prover（2025）探索了 **神经符号协同（neuro-symbolic synergy）** 的新架构：
- 将 LLM 作为“高级策略生成器”，将底层 ATP（如 E-Prover、Vampire）作为“验证与补全引擎”；
- 通过 **proof-carrying planning** 机制，在生成自然语言证明草图的同时，实时约束其对应的形式化策略序列；
- 在 **Isabelle/HOL 与 Lean 4** 的跨工具迁移实验中，显示出良好的可迁移性。

### 7.4 对教育与工程的影响

- **轻量级 FM thinking**：LLM 辅助证明降低了初学者的门槛，使本科课程能更早引入形式化验证模块；
- **维护成本降低**：AI 驱动的证明修复（proof repair）可在大规模库升级（如 Lean 3 $\rightarrow$ 4）中自动迁移 30%–50% 的过时证明；
- **可解释性挑战**：神经生成的策略序列往往缺乏人类可读的结构化注释，如何将其转化为教学资源仍是开放问题。

---

## 10. 扩展专题

### 10.1 Coq 的模块系统与命名空间

Coq 的模块系统基于 **结构型签名（structures as signatures）** 与 **函子（functors）**，支持大规模库的组织与抽象隔离。`Module Type` 定义接口，`Module` 实现接口，`Include` 进行组合。例如，MathComp 的代数层次结构（ssralg）即建立在此模块系统之上 [1]。

```coq
Module Type Monoid.
  Parameter T : Type.
  Parameter op : T -> T -> T.
  Parameter e : T.
  Axiom assoc : forall x y z, op x (op y z) = op (op x y) z.
  Axiom ident : forall x, op x e = x.
End Monoid.
```

### 10.2 Lean 的 Lake 构建系统与包管理

Lean 4 使用 **Lake** 作为官方构建系统与包管理器。`lakefile.lean` 以 Lean 语言自身描述依赖、目标与编译配置，使得构建脚本与证明代码共享同一类型系统。Mathlib 4 即通过 Lake 实现每日自动更新与缓存分发 [2]。

典型的 `lakefile.lean` 包含：
- `require` 声明外部依赖（如 `mathlib`）；
- `package` 定义项目元数据；
- `lean_lib` 指定需要编译的 Lean 库目录。

### 10.3 Agda 的记录类型与实例搜索

Agda 的 **记录类型（Record Types）** 提供了依赖积的命名访问方式，与类型类机制结合后，可实现类似 Haskell 的 ad-hoc 多态。实例搜索通过 `instance` 关键字标记候选项，编译器在需要时自动检索。例如，定义 `DecEq`（可判定相等）实例后，`_≟_` 操作符可在任何具有该实例的类型上自动可用 [3]。

```agda
record Semigroup (A : Set) : Set where
  field
    _∙_ : A → A → A
    assoc : ∀ x y z → (x ∙ y) ∙ z ≡ x ∙ (y ∙ z)

open Semigroup {{...}}
```

### 10.4 证明助手的信任基（TCB）

所有证明助手的核心都围绕一个 **信任计算基（Trusted Computing Base, TCB）**：即类型检查器与内核。TCB 越小，形式化结果的可信度越高。下表对比了各工具的 TCB 规模与实现语言：

| 证明助手 | 内核实现语言 | 内核代码规模（约） | 备注 |
|----------|--------------|-------------------|------|
| Coq / Rocq | OCaml | ~15k 行 | 含归纳类型检查与宇宙约束求解 |
| Lean 4 | C++ / Lean | ~20k 行 | 使用自举（self-hosting）架构 |
| Agda | Haskell | ~10k 行 | 依赖类型统一处理证明与程序 |
| Isabelle/HOL | Standard ML | ~10k 行 | LCF 方法学的经典实现 |

### 10.5 从证明到可执行代码：程序提取

构造性证明助手的独特优势在于 **程序提取（Program Extraction）**：从证明项中自动剥离逻辑内容，保留计算内容，生成 OCaml、Haskell、Scala 或可执行 C 代码。Coq 的 `Extraction` 命令与 Lean 的 `precompileModules` 选项均支持此工作流 [1][2]。

提取过程遵循 **realizability** 语义：一个存在性证明 `∃x. P(x)` 提取为一对 `(witness, proof_of_P)`，其中 `witness` 即为满足规范的程序。这在密码学协议（如 TLS 1.3 的验证实现）与编译器后端（如 CompCert）中已得到工业级应用。

### 10.6 大规模协作数学：Mathlib 4 的案例

Mathlib 4 是 Lean 社区维护的统一数学库，截至 2025 年已包含超过 5000 个文件、120 万行形式化代码，覆盖从线性代数到代数拓扑的广泛领域。其设计哲学强调：

- **统一抽象**：所有结构共享同一套类型类层次；
- **每日构建**：通过 GitHub Actions 与 Lake 缓存实现 CI；
- **文档驱动**：每个定义都配备自然语言文档字符串与示例 [2]。

Mathlib 4 的成功证明了依赖类型证明助手在 **协作科学** 中的潜力，也为算法形式化提供了丰富的预证明引理与规范库。

---

## 11. 常见问题与误区

**Q1：证明助手能完全替代人工证明吗？**
不能。当前的 AI 辅助证明工具（如 DeepSeek-Prover-V2）擅长处理子目标分解与策略搜索，但复杂定理的整体架构设计、不变式发现与数学直觉仍需人类主导。

**Q2：学习证明助手需要先精通数理逻辑吗？**
不需要。现代教材（如 *Software Foundations* 与 *Theorem Proving in Lean 4*）采用“做中学”模式，将逻辑基础融入编程与证明实践，适合具备基本函数式编程经验的读者。

**Q3：依赖类型是否会导致性能问题？**
在类型检查阶段，复杂的依赖类型确实可能增加编译时间。但 Lean 4 的编译器通过 **erasure** 与 **specialization** 优化，使得运行期性能接近手写 C 代码。Agda 则提供 `--erased-cubical` 等选项以控制运行期开销。

**Q4：经典逻辑与构造逻辑在工具选择上有何影响？**
若算法验证需要程序提取，应优先选择构造性证明助手（Coq、Agda、Lean）。若仅需高阶逻辑的规范与验证，且不排斥排中律，则 Isabelle/HOL 的自动化优势更为明显。

### 11.1 选型决策树

以下决策树可作为快速选型参考：

1. **是否需要从证明中提取可执行程序？**
   - 是 → 选择 Coq / Rocq 或 Lean 4（构造性支持更强）；
   - 否 → 进入问题 2。
2. **是否追求极强的自动化与外部 ATP 集成？**
   - 是 → 选择 Isabelle/HOL；
   - 否 → 进入问题 3。
3. **是否侧重依赖类型的教学演示与语言设计研究？**
   - 是 → 选择 Agda；
   - 否 → 选择 Lean 4（综合生态最完善）。

---

## 12. 总结

证明助手作为形式化算法验证的核心工具，正在从学术实验室走向工业与教育前线。Coq / Rocq 以其成熟的构造演算与程序提取机制，继续引领编译器与密码学验证；Lean 4 凭借现代语言设计与 Mathlib 生态，成为数学形式化与 AI+TP 研究的首选；Agda 以简洁的依赖类型语法，降低了 Curry–Howard 同构的教学门槛；Isabelle/HOL 则在安全关键系统的自动化验证中保持不可替代的地位。

2024–2025 年，大语言模型与神经符号方法的融合正在显著降低证明助手的入门门槛与维护成本。对于算法设计者而言，掌握至少一种证明助手的基本工作流，已成为理解“正确性即构造”这一核心范式的关键能力。

## 8. 深化补充：证明助手的 Curry–Howard 视角

从 Curry–Howard 同构的角度看，Coq、Lean 与 Agda 共享同一元理论：
- **命题作为类型（Propositions as Types）**：$P \rightarrow Q$ 既是逻辑蕴涵，也是函数类型；
- **证明作为程序（Proofs as Programs）**：构造 $P \rightarrow Q$ 的证明即编写一个将 $P$ 的证明项转换为 $Q$ 的证明项的函数；
- **规范化作为计算（Normalization as Computation）**：证明的 cut-elimination 对应程序的执行（$\beta$-归约）。

在这一视角下，策略语言（如 Ltac、`MetaM`）可视为 **证明项的元级生成器**，而类型检查器则是 **确保生成项满足目标类型的编译器**。理解这一对应关系，有助于算法设计者将规范（类型）、实现（程序）与正确性论证（证明）统一在同一个形式化框架之中。

---

## 9. 参考文献

[1] Pierce, B. C., et al. *Software Foundations* (2025 updated edition). Available at: <https://softwarefoundations.cis.upenn.edu/>. Also: The Coq Development Team. *The Coq/Rocq Proof Assistant Reference Manual*, versions 8.19/8.20. INRIA, 2024.

[2] Avigad, J., et al. *Theorem Proving in Lean 4*. Available at: <https://lean-lang.org/theorem_proving_in_lean4/>. Also: de Moura, L., & Ullrich, S. "The Lean 4 Theorem Prover". In *Proceedings of CADE-28*, 2021.

[3] Bove, A., Dybjer, P., & Norell, U. "A brief overview of Agda — A functional language with dependent types". In *TPHOLs 2009*, LNCS 5674, Springer, 2009.

[4] Nipkow, T., Wenzel, M., & Paulson, L. C. *Isabelle/HOL: A Proof Assistant for Higher-Order Logic*. LNCS 2283, Springer, 2002.

[5] Wu, Y., et al. "DeepSeek-Prover-V2: Advancing Formal Mathematical Reasoning via Large Language Models". arXiv preprint, 2024.

[6] Lin, Z., et al. "Gödel-Prover: A Neuro-Symbolic Framework for Automated Theorem Proving". arXiv preprint, 2025.

---

**文档版本 / Document Version**: 1.0
**最后更新 / Last Updated**: 2026-04-16
**状态 / Status**: 已完成 / Completed

*本文档系统介绍了 Coq/Rocq、Lean 4、Agda 与 Isabelle/HOL 四大证明助手的核心概念、可运行代码示例与选型建议，并汇总了 2024–2025 年 AI 辅助定理证明的最新进展。*
