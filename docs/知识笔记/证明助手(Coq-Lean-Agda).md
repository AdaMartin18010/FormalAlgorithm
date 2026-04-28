---
title: 证明助手(Coq Lean Agda)
version: 1.0
last_updated: 2026-04-19
---

# 证明助手 (Coq/Lean/Agda)

> **学科**: 形式化方法 / 交互式定理证明 / 类型理论
> **难度**: ★★★★☆
> **先修**: 依赖类型、Curry-Howard对应、归纳证明
> **学时**: 20小时
> **来源**: Software Foundations、Theorem Proving in Lean、TAPL
> **版本**: v1.0
> **更新**: 2026-04-09

---

## 一、核心概念

### 1.1 定义

**正式定义**:
证明助手（Proof Assistant）是基于依赖类型论的软件工具，允许用户构造形式化证明并通过机器验证其正确性。

**核心组成**:

1. **类型论核心**: 基于Martin-Löf或Calculus of Constructions
2. **证明语言**: 命令式（Coq tactics）或声明式（Agda/Lean直接构造）
3. **自动化**: 自动证明搜索、决策过程
4. **程序提取**: 从证明生成可执行代码

**三大系统对比**:

| 特性 | Coq | Lean | Agda |
|------|-----|------|------|
| 基础理论 | CIC (归纳构造演算) | CIC + 商类型 | Martin-Löf + 混合归纳 |
| 证明风格 | Tactic-based | Tactic + term | Term-based |
| 逻辑 | 构造主义 | 经典+构造主义 | 构造主义 |
| 宇宙层级 | 可预测 | 非累积 | 非累积 |
| 同伦支持 | HoTT库 | 内置 | Cubical Agda |

**直观解释**:
证明助手是"数学的编程语言"，允许用代码形式表达定义、陈述定理，并通过类型检查器验证证明。

### 1.2 属性

| 属性 | 描述 | 备注 |
|------|------|------|
| 正确性保证 | 内核小，可审计 | De Bruijn准则 |
| 交互式 | 人机协作证明 | 自动化辅助 |
| 计算内容 | 构造性证明可执行 | 程序提取 |
| 可扩展性 | 用户自定义策略/记号 | 元编程 |

### 1.3 变体

**Coq**:

- 最成熟的工业级证明助手
- 软件基础课程
- CompCert编译器验证

**Lean**:

- 微软研究院开发
- mathlib大规模数学库
- 现代编程语言特性

**Agda**:

- 强调作为编程语言
- 依赖类型编程
- Cubical Agda支持HoTT

---

## 二、关系网络

### 2.1 前置知识

| 前置知识 | 重要性 | 掌握程度检验 |
|----------|--------|--------------|
| 依赖类型 | ⭐⭐⭐⭐⭐ | Π/Σ类型 |
| Curry-Howard | ⭐⭐⭐⭐⭐ | 证明即程序 |
| 归纳证明 | ⭐⭐⭐⭐⭐ | 结构归纳 |
| 函数式编程 | ⭐⭐⭐⭐☆ | 模式匹配 |

### 2.2 思维导图

```
证明助手
├── Coq
│   ├── Gallina语言
│   ├── Ltac策略
│   ├── SSReflect
│   └── 应用: CompCert
├── Lean
│   ├── Lean 4
│   ├── mathlib
│   ├── 元编程
│   └── 应用: Liquid Tensor
└── Agda
    ├── 依赖类型编程
    ├── 混合归纳递归
    ├── Cubical扩展
    └── 应用: 类型安全库
```

---

## 三、形式化证明

### 3.1 核心原理

**Curry-Howard在证明助手中的体现**:

```
定理陈述 : 类型
证明 : 该类型的项
证明检查 : 类型检查
```

**归纳原理**:

- 对归纳类型的证明 = 对构造子的模式匹配
- 递归 = 结构递归（保证停机）

---

## 四、算法/方法详解

### 4.1 证明策略 (Coq风格)

```coq
(* 基本策略 *)
intros      (* 引入假设 *)
apply       (* 应用引理 *)
reflexivity (* 自反性 *)
rewrite     (* 重写 *)
induction   (* 归纳 *)
simpl       (* 简化 *)
tauto       (* 命题 tautology *)
omega       (* Presburger算术 *)
```

### 4.2 类型检查算法

```
算法: 依赖类型检查
输入: 上下文Γ，项t，类型T
输出: 是否Γ ⊢ t : T

1. 弱头范式化类型T
2. 根据t的形式匹配T的结构
3. 递归检查子项
4. 统一/unification处理隐式参数
```

---

## 五、示例与实例

### 5.1 Coq示例

```coq
(* 自然数定义 *)
Inductive nat : Type :=
  | O : nat
  | S : nat -> nat.

(* 加法 *)
Fixpoint plus (n m : nat) : nat :=
  match n with
  | O => m
  | S n' => S (plus n' m)
  end.

(* 证明加法交换律 *)
Theorem plus_comm : forall n m, plus n m = plus m n.
Proof.
  intros n m.
  induction n as [| n' IHn'].
  - simpl. rewrite <- plus_n_O. reflexivity.
  - simpl. rewrite IHn'. rewrite plus_n_Sm. reflexivity.
Qed.
```

### 5.2 Lean 4示例

```lean
-- 自然数定义
inductive Nat
| zero : Nat
| succ : Nat → Nat

-- 加法
def add : Nat → Nat → Nat
| Nat.zero, m => m
| Nat.succ n, m => Nat.succ (add n m)

-- 证明
theorem add_comm : ∀ n m, add n m = add m n :=
by
  intro n m
  induction n with
  | zero => simp [add]
  | succ n ih => simp [add, ih]

-- 证明即程序
def proof_as_program : ∀ n, add n Nat.zero = n :=
λ n => by simp [add]
```

### 5.3 Agda示例

```agda
-- 自然数
data ℕ : Set where
  zero : ℕ
  suc  : ℕ → ℕ

_+_ : ℕ → ℕ → ℕ
zero  + m = m
suc n + m = suc (n + m)

-- 相等类型
data _≡_ {A : Set} (x : A) : A → Set where
  refl : x ≡ x

-- 证明加法交换律（用模式匹配）
+-comm : ∀ n m → n + m ≡ m + n
+-comm zero    m = sym (+-identityʳ m)
+-comm (suc n) m =
  begin
    suc n + m    ≡⟨ refl ⟩
    suc (n + m)  ≡⟨ cong suc (+-comm n m) ⟩
    suc (m + n)  ≡⟨ sym (+-suc m n) ⟩
    m + suc n    ∎
  where open ≡-Reasoning

-- 直接使用等式推理的替代方式
+-comm' : ∀ n m → n + m ≡ m + n
+-comm' zero    m = sym (+-identityʳ m)
+-comm' (suc n) m rewrite +-comm' n m | +-suc m n = refl
```

### 5.4 高级示例：列表反转

**Coq**:

```coq
(* 列表定义 *)
Inductive list (A : Type) : Type :=
  | nil : list A
  | cons : A -> list A -> list A.

Arguments nil {A}.
Arguments cons {A} _ _.

(* 追加 *)
Fixpoint app {A} (l1 l2 : list A) : list A :=
  match l1 with
  | nil => l2
  | cons x xs => cons x (app xs l2)
  end.

(* 反转 *)
Fixpoint rev {A} (l : list A) : list A :=
  match l with
  | nil => nil
  | cons x xs => app (rev xs) (cons x nil)
  end.

(* 证明: rev (rev l) = l *)
Lemma rev_involutive : forall A (l : list A), rev (rev l) = l.
Proof.
  intros A l. induction l as [| x xs IH].
  - reflexivity.
  - simpl. rewrite rev_app_distr. rewrite IH. reflexivity.
Qed.
```

**Lean 4**:

```lean
inductive List (α : Type)
| nil : List α
| cons : α → List α → List α

def append : List α → List α → List α
| .nil, bs => bs
| .cons a as, bs => .cons a (append as bs)

def reverse : List α → List α
| .nil => .nil
| .cons a as => append (reverse as) (.cons a .nil)

theorem reverse_involutive : ∀ (l : List α), reverse (reverse l) = l
| .nil => rfl
| .cons a as => by
  simp [reverse, reverse_append, reverse_involutive as]
```

---

## 六、习题

### 6.1 理解题 (L1-L2)

1. **基本证明** [难度⭐]

   用Coq或Agda证明：∀ n, n + 0 = n

   <details>
   <summary>解答 (Coq)</summary>

   ```coq
   Theorem plus_n_O : forall n, n + 0 = n.
   Proof.
     intros n. induction n.
     - reflexivity.
     - simpl. rewrite IHn. reflexivity.
   Qed.
   ```

   </details>

2. **列表长度** [难度⭐]

   定义列表长度函数并证明：length (app l1 l2) = length l1 + length l2

   <details>
   <summary>解答 (Agda)</summary>

   ```agda
   length : ∀ {A} → List A → ℕ
   length [] = 0
   length (_ ∷ xs) = 1 + length xs

   length-++ : ∀ {A} (xs ys : List A) →
               length (xs ++ ys) ≡ length xs + length ys
   length-++ [] ys = refl
   length-++ (x ∷ xs) ys = cong suc (length-++ xs ys)
   ```

   </details>

### 6.2 应用题 (L3)

1. **树遍历** [难度⭐⭐]

   定义二叉树和它的中序遍历，证明遍历长度等于节点数。

   <details>
   <summary>解答 (Lean)</summary>

   ```lean
   inductive Tree (α : Type)
   | leaf : Tree α
   | node : Tree α → α → Tree α → Tree α

   def inorder : Tree α → List α
   | .leaf => []
   | .node l x r => inorder l ++ [x] ++ inorder r

   def size : Tree α → Nat
   | .leaf => 0
   | .node l _ r => 1 + size l + size r

   theorem inorder_length : ∀ t, (inorder t).length = size t
   | .leaf => rfl
   | .node l x r => by
     simp [inorder, size, List.length_append, inorder_length l, inorder_length r]
   ```

   </details>

### 6.3 证明题 (L4-L5)

1. **归纳原理** [难度⭐⭐⭐]

   证明：良基归纳原理可以从自然数归纳导出。

   <details>
   <summary>解答 (Coq)</summary>

   ```coq
   Require Import Wellfounded.

   Theorem nat_induction_wf :
     forall P : nat -> Prop,
     P 0 ->
     (forall n, (forall m, m < n -> P m) -> P n) ->
     forall n, P n.
   Proof.
     intros P H0 Hstep n.
     induction n using (well_founded_induction lt_wf).
     apply Hstep. exact H.
   Qed.
   ```

   </details>

2. **Red-Black树** [难度⭐⭐⭐⭐]

   定义红黑树不变量，证明插入保持平衡。

   <details>
   <summary>解答概要</summary>

   这是大型证明，通常需要：
   - 定义颜色、树类型
   - 定义平衡不变量（黑高、红节点无红子）
   - 定义插入并修复
   - 分情况证明不变量保持

   参考: Coq标准库MSetRBT或Lean的mathlib

   </details>

---

## 七、应用场景

### 7.1 经典应用

| 项目 | 描述 | 系统 |
|------|------|------|
| CompCert | 验证C编译器 | Coq |
| seL4 | 操作系统微内核 | Isabelle/HOL |
| mathlib | 现代数学库 | Lean |
| UniMath | 同伦类型论 | Coq |
| 四色定理 | 图论定理 | Coq |
| Liquid Tensor | 凝聚数学 | Lean |

### 7.2 实际案例

**案例**: CompCert编译器验证

**背景**:
用Coq证明C编译器正确性。

**规模**:

- ~10万行Coq代码
- 覆盖C大部分语义
- 机器生成代码证明正确

**影响**:

- 航空、核能领域使用
- 证明辅助验证的新标准

---

## 八、多维对比

| 维度 | Coq | Lean 4 | Agda |
|------|-----|--------|------|
| 学习曲线 | 陡峭 | 中等 | 中等 |
| 数学库 | MathComp | mathlib | 基础 |
| 编程体验 | 一般 | 优秀 | 良好 |
| 自动化 | 强 | 中等 | 弱 |
| IDE支持 | CoqIDE/VSC | VSC完善 | Emacs/VSC |
| 社区规模 | 大 | 快速增长 | 学术 |

---

## 九、扩展阅读

### 9.1 教材

| 资源 | 链接 | 推荐度 |
|------|------|--------|
| Software Foundations | softwarefoundations.cis.upenn.edu | ⭐⭐⭐⭐⭐ |
| Theorem Proving in Lean | leanprover.github.io | ⭐⭐⭐⭐⭐ |
| Programming Language Foundations in Agda | plfa.inf.ed.ac.uk | ⭐⭐⭐⭐⭐ |

### 9.2 在线资源

- **Coq**: <https://coq.inria.fr/>
- **Lean**: <https://leanprover.github.io/>
- **Agda**: <https://agda.readthedocs.io/>

---

## 十、专家批注

> **Georges Gonthier** (MathComp/四色定理):
> "形式化证明不是替代数学直觉，而是确保我们的直觉建立在坚实的基础上。"

> **Kevin Buzzard** (mathlib):
> "Lean和mathlib正在改变数学家工作的方式——未来20年，形式化将成为常态。"

---

## 十一、修订历史

| 版本 | 日期 | 修订者 | 修订内容 |
|------|------|--------|----------|
| v1.0 | 2026-04-09 | FormalAlgorithm Team | 初始版本 |

---

**标签**: #证明助手 #Coq #Lean #Agda #定理证明

**相关笔记**:

- [依赖类型.md](./依赖类型.md)
- [Curry-Howard对应.md](./Curry-Howard对应.md)
- [同伦类型论.md](./同伦类型论.md)
