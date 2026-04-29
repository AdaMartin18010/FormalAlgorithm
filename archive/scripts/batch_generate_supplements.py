#!/usr/bin/env python3
"""Batch generate missing 六维补充 documents."""

from pathlib import Path

SUPPLEMENTS = [
    # 06-逻辑系统 (5)
    {
        "path": "docs/06-逻辑系统/05-多值逻辑理论-六维补充.md",
        "title": "05-多值逻辑理论-六维补充",
        "category": "06-逻辑系统",
        "concepts": ["多值逻辑", "真值度", "模糊逻辑", "MV代数"],
        "content": """---
title: 05-多值逻辑理论-六维补充
category: 06-逻辑系统
concepts: ["多值逻辑", "真值度", "模糊逻辑", "MV代数"]
level: 中级
---

# 多值逻辑理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Gottwald (2001) A Treatise on Many-Valued Logics; Hájek (1998) Metamathematics of Fuzzy Logic

---

## 一、规范定义深化

### 1.1 多值逻辑的形式化定义

**定义 1.1 (多值逻辑)** 多值逻辑（Many-Valued Logic, MVL）是经典二值逻辑的扩展，其真值集为 $V$，其中 $|V| \geq 3$。一个多值逻辑系统由四元组 $(V, \mathcal{L}, \mathcal{A}, \mathcal{D})$ 定义：

- **真值集 $V$**: 有限集 $\{0, \frac{1}{n-1}, \ldots, \frac{n-2}{n-1}, 1\}$ 或无限集 $[0, 1]$
- **语言 $\mathcal{L}$**: 命题变元集合与连接词集合（$\neg, \wedge, \vee, \rightarrow$）
- **代数结构 $\mathcal{A}$**: 定义在 $V$ 上的运算语义
- **指定值集 $\mathcal{D} \subseteq V$**: 满足 $\top \in \mathcal{D}$，表示"真"的真值子集

**定义 1.2 (Łukasiewicz 逻辑)** Łukasiewicz $n$ 值逻辑的蕴含与否定定义为：
$$x \rightarrow y = \min(1, 1 - x + y), \quad \neg x = 1 - x$$

**定义 1.3 (模糊逻辑)** 当 $V = [0, 1]$ 时，若采用三角模（t-norm）$T$ 与剩余蕴含 $I_T$ 作为合取与蕴含的语义，则称为模糊逻辑。

---

## 二、模型设计深化

### 2.1 代数语义模型

多值逻辑的语义可通过代数结构刻画：

| 逻辑系统 | 代数结构 | 关键性质 |
|----------|----------|----------|
| Łukasiewicz 逻辑 | MV-代数 | 布尔代数的推广，满足 Chang 公理 |
| Gödel 逻辑 | Gödel 代数（Heyting 链）| 幂等性 $x \wedge x = x$ |
| 乘积逻辑 | 乘积代数 | 消去律 $x \cdot y = x \cdot z \Rightarrow y = z$（$x > 0$）|
| 基本逻辑 BL | BL-代数 | 连续 t-norm 的代数抽象 |

**定理 2.1 (MV-代数完备性)** Łukasiewicz 逻辑在 MV-代数类中完备。

### 2.2 标准完备性

**定理 2.2 (Hájek 标准完备性)** BL 逻辑在由连续 t-norm 生成的标准代数 $([0, 1], *, \rightarrow, 0, 1)$ 中完备。

---

## 三、数学符号与推导

### 3.1 连续 t-norm 的分类（Mostert-Shields 定理）

**定理 3.1** 任何连续 t-norm $*$ 都同构于下列三种基本 t-norm的序和（ordinal sum）：
1. **最小 t-norm**（Gödel）: $x *_G y = \min(x, y)$
2. **乘积 t-norm**: $x *_P y = x \cdot y$
3. **Łukasiewicz t-norm**: $x *_L y = \max(0, x + y - 1)$

### 3.2 可满足性复杂度

| 逻辑 | 可满足性复杂度 |
|------|---------------|
| 经典命题逻辑 | NP-完全 |
| Łukasiewicz $n$ 值逻辑 | NP-完全 |
| 基本命题模糊逻辑 | NP-完全 |
| 一阶模糊逻辑 | $\Pi_2$-完全 |

---

## 四、示例性代码

```rust
/// Łukasiewicz 蕴含与 t-norm
pub fn lukasiewicz_implication(x: f64, y: f64) -> f64 {
    (1.0 - x + y).min(1.0)
}

pub fn lukasiewicz_tnorm(x: f64, y: f64) -> f64 {
    (x + y - 1.0).max(0.0)
}

/// Gödel 蕴含与 t-norm
pub fn godel_implication(x: f64, y: f64) -> f64 {
    if x <= y { 1.0 } else { y }
}

pub fn godel_tnorm(x: f64, y: f64) -> f64 {
    x.min(y)
}

/// 乘积蕴含与 t-norm
pub fn product_implication(x: f64, y: f64) -> f64 {
    if x <= y { 1.0 } else { y / x }
}

pub fn product_tnorm(x: f64, y: f64) -> f64 {
    x * y
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lukasiewicz() {
        assert!((lukasiewicz_implication(0.3, 0.7) - 1.0).abs() < 1e-9);
        assert!((lukasiewicz_tnorm(0.3, 0.7) - 0.0).abs() < 1e-9);
    }

    #[test]
    fn test_godel() {
        assert_eq!(godel_implication(0.3, 0.7), 1.0);
        assert_eq!(godel_tnorm(0.3, 0.7), 0.3);
    }
}
```

---

## 五、形式化证明

### 5.1 MV-代数基本定律的 Lean4 草图

```lean4
-- MV-代数定义：含二元运算 ⊕、一元运算 ¬、常数 0 的代数结构
class MVAlgebra (α : Type) where
  add : α → α → α      -- ⊕
  neg : α → α          -- ¬
  zero : α             -- 0
  -- Chang 公理
  associativity : ∀ x y z, add (add x y) z = add x (add y z)
  commutativity : ∀ x y, add x y = add y x
  identity : ∀ x, add x zero = x
  involution : ∀ x, neg (neg x) = x
  mv_axiom : ∀ x y, neg (add (neg x) y) = add (neg (add (neg x) (neg y))) y
```

---

## 六、引用来源

1. [Gottwald2001] Gottwald, S. (2001). *A Treatise on Many-Valued Logics*. Research Studies Press.
2. [Hajek1998] Hájek, P. (1998). *Metamathematics of Fuzzy Logic*. Kluwer.
3. [Chang1958] Chang, C. C. (1958). "Algebraic Analysis of Many Valued Logics." *Transactions of the AMS*, 88(2), 467–490.
4. [Cignoli2000] Cignoli, R., d'Ottaviano, I. M. L., & Mundici, D. (2000). *Algebraic Foundations of Many-Valued Reasoning*. Kluwer.
5. [Novak1999] Novák, V., Perfilieva, I., & Močkoř, J. (1999). *Mathematical Principles of Fuzzy Logic*. Kluwer.
"""
    },
    {
        "path": "docs/06-逻辑系统/06-线性逻辑-六维补充.md",
        "title": "06-线性逻辑-六维补充",
        "category": "06-逻辑系统",
        "concepts": ["线性逻辑", "资源敏感", "证明网", "相位语义"],
        "content": """---
title: 06-线性逻辑-六维补充
category: 06-逻辑系统
concepts: ["线性逻辑", "资源敏感", "证明网", "相位语义"]
level: 高级
---

# 线性逻辑 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Girard (1987) Linear Logic; Troelstra (1992) Lectures on Linear Logic

---

## 一、规范定义深化

### 1.1 线性逻辑的形式化定义

**定义 1.1 (线性逻辑)** 线性逻辑（Linear Logic, LL）由 Jean-Yves Girard 于 1987 年提出，核心特征是**资源敏感性**：每个假设必须且只能使用一次。

**连接词分类**:

| 类别 | 乘法型 | 加法型 |
|------|--------|--------|
| 合取 | $\otimes$（张量） | $\&$（with） |
| 析取 | $\par$（par） | $\oplus$（oplus） |
| 蕴涵 | $\multimap$（线性蕴涵） | — |

**模态**:
- **!** (of course / bang): 资源可任意复制和丢弃
- **?** (why not): 对偶模态

** sequent 演算规则**:
$$\frac{\Gamma \vdash A \quad \Delta \vdash B}{\Gamma, \Delta \vdash A \otimes B} \; (\otimes_R)$$

### 1.2 直觉主义线性逻辑 (ILL)

ILL 是线性逻辑的直觉主义片段， sequent 形式为 $\Gamma \vdash A$（单结论）。

---

## 二、模型设计深化

### 2.1 相位语义 (Phase Semantics)

**定义 2.1** 设 $(M, \cdot, 1)$ 为交换幺半群，$\bot \subseteq M$ 为极点集。定义对偶运算：
$$X^\bot = \{m \in M : \forall x \in X, m \cdot x \in \bot\}$$

**事实 (facts)**: 满足 $X = X^{\bot\bot}$ 的子集。

**线性逻辑连接词的语义**:
- $X \otimes Y = (X \cdot Y)^{\bot\bot}$
- $X \par Y = (X^\bot \cdot Y^\bot)^\bot$
- $!X = (X \cap I)^{\bot\bot}$，其中 $I$ 为幂等元集合

**完备性定理**: 线性逻辑在相位语义中完备。

### 2.2 相干空间语义

**定义 2.2 (相干空间)** 相干空间 $X$ 是带自反、对称关系的 Web 集合 $|X|$。

- $a \sim a$（自反）
- $a \sim b \Rightarrow b \sim a$（对称）

线性蕴涵 $X \multimap Y$ 的 Web 为 $|X| \times |Y|$，相干关系为：
$$(a, b) \sim (a', b') \iff (a \sim a' \Rightarrow b \sim b') \wedge (b \neq b' \Rightarrow a \neq a')$$

---

## 三、数学符号与推导

### 3.1 证明网 (Proof Nets)

证明网是线性逻辑证明的图形化表示，消除了 sequent 演算中的冗余（如交换规则）。

**正确性准则 (Danos-Regnier)**:
1. 每个 $\otimes$ 节点连接两个子网
2. 每个 $\par$ 节点合并两个子网
3. 对任意切换（switching），得到的图是一棵树且无环

**定理 3.1 (顺序化)** 一个证明网对应一个 sequent 演算证明当且仅当它满足 Danos-Regnier 正确性准则。

### 3.2 割消定理

**定理 3.2** 线性逻辑中的割规则可完全消去，且割消过程终止。

---

## 四、示例性代码

```rust
/// 线性类型系统模拟（所有权模型）
/// 通过 Rust 所有权系统直观展示线性逻辑的资源敏感性

#[derive(Debug, Clone)]
pub struct LinearResource<T> {
    value: T,
    consumed: bool,
}

impl<T> LinearResource<T> {
    pub fn new(value: T) -> Self {
        Self { value, consumed: false }
    }

    /// 线性使用：消费资源后返回结果
    pub fn consume<F, R>(mut self, f: F) -> R
    where
        F: FnOnce(T) -> R,
    {
        self.consumed = true;
        f(self.value)
    }

    /// !T（bang）：复制资源（需实现 Clone）
    pub fn duplicate(&self) -> (Self, Self)
    where
        T: Clone,
    {
        assert!(!self.consumed, "Resource already consumed");
        (
            Self::new(self.value.clone()),
            Self::new(self.value.clone()),
        )
    }
}

impl<T> Drop for LinearResource<T> {
    fn drop(&mut self) {
        if !self.consumed {
            panic!("Linear resource dropped without consumption!");
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_linear_consume() {
        let r = LinearResource::new(42);
        let result = r.consume(|v| v * 2);
        assert_eq!(result, 84);
    }

    #[test]
    fn test_duplicate() {
        let r = LinearResource::new(10);
        let (r1, r2) = r.duplicate();
        let a = r1.consume(|v| v + 1);
        let b = r2.consume(|v| v + 2);
        assert_eq!((a, b), (11, 12));
    }
}
```

---

## 五、形式化证明

### 5.1 线性逻辑割消的 Lean4 草图

```lean4
-- 线性逻辑公式归纳定义
inductive LLFormula
  | atom (A : String)
  | tensor (A B : LLFormula)      -- A ⊗ B
  | par (A B : LLFormula)         -- A ⅋ B
  | lolli (A B : LLFormula)       -- A ⊸ B
  | bang (A : LLFormula)          -- !A
  | one                           -- 1
  | bot                           -- ⊥

-- 证明网节点（简化表示）
inductive ProofNetNode
  | axiom (A : LLFormula)
  | cut (A : LLFormula)
  | tensor (left right : ProofNetNode)
  | par (left right : ProofNetNode)

-- 割消归约步骤
def cutEliminationStep (n : ProofNetNode) : Option ProofNetNode :=
  match n with
  | .cut A (.axiom A') => if A = A' then .none else .some n
  | .cut (.tensor A B) (.par A' B') =>
      if A = A' ∧ B = B' then
        .some (.cut A (.axiom A)) -- 简化示例
      else .some n
  | _ => .some n
```

---

## 六、引用来源

1. [Girard1987] Girard, J.-Y. (1987). "Linear Logic." *Theoretical Computer Science*, 50(1), 1–101.
2. [Troelstra1992] Troelstra, A. S. (1992). *Lectures on Linear Logic*. CSLI Publications.
3. [Girard1995] Girard, J.-Y. (1995). "Linear Logic: Its Syntax and Semantics." In *Advances in Linear Logic*, Cambridge University Press.
4. [Mellies2009] Melliès, P.-A. (2009). "Categorical Semantics of Linear Logic." *Panoramas et Synthèses*, 27.
5. [Danos1989] Danos, V., & Regnier, L. (1989). "The Structure of Multiplicatives." *Archive for Mathematical Logic*, 28(3), 181–203.
"""
    },
    {
        "path": "docs/06-逻辑系统/07-时序逻辑-六维补充.md",
        "title": "07-时序逻辑-六维补充",
        "category": "06-逻辑系统",
        "concepts": ["时序逻辑", "LTL", "CTL", "模型检测", "Büchi自动机"],
        "content": """---
title: 07-时序逻辑-六维补充
category: 06-逻辑系统
concepts: ["时序逻辑", "LTL", "CTL", "模型检测", "Büchi自动机"]
level: 高级
---

# 时序逻辑 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Baier & Katoen (2008) Principles of Model Checking; Clarke et al. (1999) Model Checking

---

## 一、规范定义深化

### 1.1 时序逻辑的形式化定义

**定义 1.1 (时序逻辑)** 时序逻辑（Temporal Logic）扩展了经典逻辑，引入时序算子以描述系统行为随时间演化的性质。

**线性时序逻辑 (LTL)** 算子：
- **$\mathbf{X} \phi$** (Next): $\phi$ 在下一时刻成立
- **$\mathbf{F} \phi$** (Eventually/Future): $\phi$ 在未来某时刻成立
- **$\mathbf{G} \phi$** (Globally/Always): $\phi$ 在所有未来时刻成立
- **$\phi \mathbf{U} \psi$** (Until): $\psi$ 在未来某时刻成立，且在此之前 $\phi$ 一直成立

**计算树逻辑 (CTL)** 算子（路径量词 + 时序算子）：
- **$\mathbf{A} \phi$**: 所有路径上 $\phi$ 成立
- **$\mathbf{E} \phi$**: 存在某条路径使 $\phi$ 成立
- CTL* 同时包含路径量词和 LTL 算子

### 1.2 语义

**LTL 语义**（基于无限字/路径 $\pi = s_0 s_1 s_2 \ldots$）：
$$\pi \models \mathbf{X} \phi \iff \pi^1 \models \phi$$
$$\pi \models \phi \mathbf{U} \psi \iff \exists i \geq 0: (\pi^i \models \psi \wedge \forall 0 \leq j < i: \pi^j \models \phi)$$

其中 $\pi^i = s_i s_{i+1} \ldots$ 为从第 $i$ 个状态开始的后缀。

---

## 二、模型设计深化

### 2.1 Kripke 结构

**定义 2.1 (Kripke 结构)** 用于模型检测的迁移系统 $M = (S, S_0, R, L)$：
- $S$: 有限状态集合
- $S_0 \subseteq S$: 初始状态集合
- $R \subseteq S \times S$: 全迁移关系（每个状态至少有一条出边）
- $L: S \to 2^{AP}$: 标记函数，将每个状态映射到其成立的原子命题集合

### 2.2 模型检测算法

**LTL 模型检测**:
1. 将 $\neg \phi$ 转换为 Büchi 自动机 $A_{\neg\phi}$
2. 将 Kripke 结构 $M$ 转换为 Büchi 自动机 $A_M$
3. 检查乘积自动机 $A_M \times A_{\neg\phi}$ 的语言是否为空
4. 若非空，则 $M \not\models \phi$，并给出反例路径

**复杂度**: LTL 模型检测为 PSPACE-完全；CTL 模型检测为 P-完全（线性时间 $O(|M| \cdot |\phi|)$）。

---

## 三、数学符号与推导

### 3.1 CTL 模型检测的不动点刻画

CTL 算子可表示为最小/最大不动点：

$$\mathbf{EF} \phi = \mu Z. (\phi \vee \mathbf{EX} Z)$$
$$\mathbf{EG} \phi = \nu Z. (\phi \wedge \mathbf{EX} Z)$$
$$\mathbf{AF} \phi = \mu Z. (\phi \vee \mathbf{AX} Z)$$
$$\mathbf{AG} \phi = \nu Z. (\phi \wedge \mathbf{AX} Z)$$

其中 $\mu$ 为最小不动点，$\nu$ 为最大不动点。

### 3.2 不动点迭代算法

**算法** (计算 $\mathbf{EF} \phi$):
1. $Z_0 = \emptyset$
2. $Z_{i+1} = \phi \cup \{s \in S : \exists t \in Z_i, (s, t) \in R\}$
3. 直到 $Z_{i+1} = Z_i$

**终止性**: 因 $S$ 有限且 $Z_i$ 单调递增，最多 $|S|$ 步收敛。

---

## 四、示例性代码

```rust
/// 简单的 Kripke 结构与 LTL/CTL 语义模拟
use std::collections::{HashMap, HashSet};

type StateId = usize;

#[derive(Debug, Clone)]
pub struct KripkeStructure {
    pub states: Vec<StateId>,
    pub transitions: HashMap<StateId, Vec<StateId>>,
    pub labels: HashMap<StateId, HashSet<String>>,
}

impl KripkeStructure {
    pub fn new() -> Self {
        Self {
            states: Vec::new(),
            transitions: HashMap::new(),
            labels: HashMap::new(),
        }
    }

    pub fn add_state(&mut self, id: StateId, labels: HashSet<String>) {
        self.states.push(id);
        self.labels.insert(id, labels);
        self.transitions.insert(id, Vec::new());
    }

    pub fn add_transition(&mut self, from: StateId, to: StateId) {
        self.transitions.get_mut(&from).unwrap().push(to);
    }

    /// 检查 CTL 公式 EF φ：从初始状态出发是否存在路径最终满足 φ
    pub fn check_ef(&self, phi: impl Fn(StateId) -> bool) -> bool {
        let mut reachable = HashSet::new();
        let mut stack: Vec<StateId> = self.states.clone();
        while let Some(s) = stack.pop() {
            if phi(s) {
                return true;
            }
            if reachable.insert(s) {
                if let Some(next) = self.transitions.get(&s) {
                    for &n in next {
                        if !reachable.contains(&n) {
                            stack.push(n);
                        }
                    }
                }
            }
        }
        false
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_kripke_ef() {
        let mut ks = KripkeStructure::new();
        ks.add_state(0, ["a".to_string()].into_iter().collect());
        ks.add_state(1, ["b".to_string()].into_iter().collect());
        ks.add_state(2, ["c".to_string()].into_iter().collect());
        ks.add_transition(0, 1);
        ks.add_transition(1, 2);
        assert!(ks.check_ef(|s| s == 2));
        assert!(!ks.check_ef(|s| s == 5));
    }
}
```

---

## 五、形式化证明

### 5.1 LTL 与 Büchi 自动机等价性

**定理 5.1** 对任意 LTL 公式 $\phi$，存在 Büchi 自动机 $A_\phi$ 使得 $L(A_\phi) = \{\pi : \pi \models \phi\}$。

*构造概要*（Vardi-Wolper 构造）:
1. 定义公式的闭包 $cl(\phi)$（所有子公式及其否定）
2. 状态为 $cl(\phi)$ 的极大一致子集（Hintikka 集）
3. 迁移关系保证时序算子的局部一致性
4. 接受条件确保 $\mathbf{U}$ 和 $\mathbf{F}$ 的语义

---

## 六、引用来源

1. [Baier2008] Baier, C., & Katoen, J.-P. (2008). *Principles of Model Checking*. MIT Press.
2. [Clarke1999] Clarke, E. M., Grumberg, O., & Peled, D. A. (1999). *Model Checking*. MIT Press.
3. [Pnueli1977] Pnueli, A. (1977). "The Temporal Logic of Programs." *FOCS*, 46–57.
4. [Vardi1986] Vardi, M. Y., & Wolper, P. (1986). "An Automata-Theoretic Approach to Automatic Program Verification." *LICS*, 332–344.
5. [Queille1982] Queille, J. P., & Sifakis, J. (1982). "Specification and Verification of Concurrent Systems in CESAR." *International Symposium on Programming*, 337–351.
"""
    },
    {
        "path": "docs/06-逻辑系统/SMT求解器-六维补充.md",
        "title": "SMT求解器-六维补充",
        "category": "06-逻辑系统",
        "concepts": ["SMT", "SAT", "决策过程", "Egraph", "DPLL(T)"],
        "content": """---
title: SMT求解器-六维补充
category: 06-逻辑系统
concepts: ["SMT", "SAT", "决策过程", "Egraph", "DPLL(T)"]
level: 高级
---

# SMT 求解器 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Kroening & Strichman (2016) Decision Procedures; Barrett & Tinelli (2018) Satisfiability Modulo Theories

---

## 一、规范定义深化

### 1.1 SMT 问题的形式化定义

**定义 1.1 (SMT)** 可满足性模理论（Satisfiability Modulo Theories, SMT）问题是判定一阶逻辑公式在特定背景理论 $T$ 下的可满足性。

**输入**: 一阶逻辑公式 $\phi$，其中函数/谓词符号来自签名 $\Sigma$
**理论 $T$**: 对 $\Sigma$ 的特定解释（如线性实数算术、位向量、数组等）
**输出**: 
- **SAT**: 存在模型 $M \models_T \phi$
- **UNSAT**: $T \models \neg \phi$
- **UNKNOWN**: 无法判定（一般而言 SMT 为半可判定）

### 1.2 常见理论片段

| 理论 | 名称 | 判定复杂度 | 典型应用 |
|------|------|-----------|----------|
| QF_LRA | 无量词线性实数算术 | P | 混合系统验证 |
| QF_LIA | 无量词线性整数算术 | NP-完全 | 程序分析 |
| QF_BV | 无量词位向量 | NP-完全 | 硬件验证 |
| QF_AUFLIA | 数组+未解释函数+线性整数 | NP-完全 | 软件验证 |
| LIA | 含量词线性整数 | 不可判定 | — |

---

## 二、模型设计深化

### 2.1 DPLL(T) 架构

SMT 求解器通常采用 **DPLL(T)** 架构，结合 SAT 求解器与理论求解器：

1. **抽象**: 将原子公式替换为布尔变量，得到命题公式 $\phi_{bool}$
2. **DPLL**: 使用 CDCL（冲突驱动子句学习）SAT 求解器搜索 $\phi_{bool}$ 的满足赋值
3. **理论检查**: 对每个布尔赋值，检查对应的原子公式集合是否在理论 $T$ 中一致
4. **冲突学习**: 若理论不一致，学习冲突子句并回溯

**关键接口**: 
- **Check-SAT**: 理论求解器判定当前赋值是否 $T$-一致
- **Explain**: 理论求解器返回最小不一致子集（用于学习）
- **Propagate**: 理论求解器推导隐含赋值

### 2.2 Nelson-Oppen 组合方法

**定理 2.1** 若理论 $T_1$ 和 $T_2$ 满足：
1. 量词自由、有限签名、不相交（除等号外无共享符号）
2. 都是稳定无限的（stably infinite）

则 $T_1 \cup T_2$ 的判定问题可规约到各自的判定问题，通过**等号传播**（equality propagation）实现。

---

## 三、数学符号与推导

### 3.1 单纯形法（线性实数算术）

理论求解器将公式转化为标准形式：
$$A x = 0, \quad l_i \leq x_i \leq u_i$$

**基本变量**与**非基本变量**的划分。每次 pivot 操作保持等式系统的等价性。

**终止性**: 若使用 Bland 规则避免循环，单纯形法在实数域终止。

### 3.2 Congruence Closure（未解释函数）

**定义 3.1** 给定项集合 $T$ 和等式集合 $E$，congruence closure 是满足以下条件的等价关系 $\sim$：
1. **自反、对称、传递**: 等价关系
2. **包含 $E$**: $s = t \in E \Rightarrow s \sim t$
3. **Congruence**: $s_1 \sim t_1, \ldots, s_n \sim t_n \Rightarrow f(s_1,\ldots,s_n) \sim f(t_1,\ldots,t_n)$

**算法**: 使用 Union-Find 数据结构维护等价类，时间 $O(|T| \alpha(|T|))$。

---

## 四、示例性代码

```rust
/// Union-Find with congruence closure (simplified)
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        Self {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }

    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }

    pub fn union(&mut self, x: usize, y: usize) {
        let (rx, ry) = (self.find(x), self.find(y));
        if rx == ry { return; }
        match self.rank[rx].cmp(&self.rank[ry]) {
            std::cmp::Ordering::Less => self.parent[rx] = ry,
            std::cmp::Ordering::Greater => self.parent[ry] = rx,
            std::cmp::Ordering::Equal => {
                self.parent[ry] = rx;
                self.rank[rx] += 1;
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);
        uf.union(0, 1);
        uf.union(2, 3);
        assert_eq!(uf.find(0), uf.find(1));
        assert_ne!(uf.find(0), uf.find(2));
        uf.union(1, 2);
        assert_eq!(uf.find(0), uf.find(3));
    }
}
```

---

## 五、形式化证明

### 5.1 DPLL(T) 完备性

**定理 5.1** 若理论 $T$ 的量词自由片段可判定，则 DPLL(T) 对无量词公式是完备且可靠的。

*证明概要*:
- **可靠性**: SAT 求解器仅生成命题一致的赋值，理论求解器进一步保证 $T$-一致性
- **完备性**: 若公式 $T$-不可满足，有限搜索空间保证 DPLL 最终会遍历所有赋值或通过学习子句剪枝全部搜索空间

---

## 六、引用来源

1. [Kroening2016] Kroening, D., & Strichman, O. (2016). *Decision Procedures: An Algorithmic Point of View* (2nd ed.). Springer.
2. [Barrett2018] Barrett, C., & Tinelli, C. (2018). "Satisfiability Modulo Theories." In *Handbook of Model Checking*, Springer.
3. [Nelson1979] Nelson, G., & Oppen, D. C. (1979). "Simplification by Cooperating Decision Procedures." *TOPLAS*, 1(2), 245–257.
4. [Dutertre2006] Dutertre, B., & de Moura, L. (2006). "A Fast Linear-Arithmetic Solver for DPLL(T)." *CAV*, 81–94.
5. [deMoura2008] de Moura, L., & Bjørner, N. (2008). "Z3: An Efficient SMT Solver." *TACAS*, 337–340.
"""
    },
    {
        "path": "docs/06-逻辑系统/09-时序逻辑理论-六维补充.md",
        "title": "09-时序逻辑理论-六维补充",
        "category": "06-逻辑系统",
        "concepts": ["时序逻辑理论", "CTL*", "公平性", "抽象解释", "符号模型检测"],
        "content": """---
title: 09-时序逻辑理论-六维补充
category: 06-逻辑系统
concepts: ["时序逻辑理论", "CTL*", "公平性", "抽象解释", "符号模型检测"]
level: 专家
---

# 时序逻辑理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Emerson (1990) Temporal and Modal Logic; Kupferman et al. (2000) An Automata-Theoretic Approach to Branching-Time Model Checking

---

## 一、规范定义深化

### 1.1 CTL* 的统一框架

**定义 1.1 (CTL*)** CTL* 合并了 LTL 的路径量词自由性和 CTL 的分支量词，其语法分为**状态公式** $\Phi$ 和**路径公式** $\phi$：

$$\Phi ::= p \mid \neg \Phi \mid \Phi \wedge \Phi \mid \mathbf{A}\phi \mid \mathbf{E}\phi$$
$$\phi ::= \Phi \mid \neg \phi \mid \phi \wedge \phi \mid \mathbf{X}\phi \mid \phi \mathbf{U} \phi$$

**表达力层级**: CTL $\subset$ CTL*，LTL $\subset$ CTL*，且 CTL 与 LTL 不可比较。

### 1.2 公平性约束

**定义 1.2 (公平性)** 路径 $\pi$ 满足弱公平性（justice）条件 $\mathcal{J} = \{J_1, \ldots, J_k\}$ 若：
$$\forall J \in \mathcal{J}: \mathbf{G}\mathbf{F} J$$

即 $J$ 中的某状态在路径上无限频繁出现。

**强公平性**（compassion）: $\mathbf{G}\mathbf{F} p \rightarrow \mathbf{G}\mathbf{F} q$

---

## 二、模型设计深化

### 2.1 符号模型检测 (Symbolic Model Checking)

使用**有序二叉决策图**（Ordered Binary Decision Diagrams, OBDD）表示状态集合和迁移关系：

- **状态集合 $S$**: 布尔函数 $f_S(v_1, \ldots, v_n)$
- **迁移关系 $R$**: 布尔函数 $f_R(v_1, \ldots, v_n, v'_1, \ldots, v'_n)$

**像计算**:
$$Img(S, R) = \exists v_1, \ldots, v_n: f_S(v) \wedge f_R(v, v')$$

**前像计算**:
$$PreImg(S, R) = \exists v'_1, \ldots, v'_n: f_R(v, v') \wedge f_S(v')$$

### 2.2 抽象解释与模型检测

**Galois 连接**: $(\alpha, \gamma)$ 连接具体域 $C$ 与抽象域 $A$：
$$\alpha: C \to A, \quad \gamma: A \to C$$

**抽象模型检测**: 在抽象域上验证性质，利用 $M \models \phi \Rightarrow \alpha(M) \models \alpha(\phi)$ 进行安全近似。

---

## 三、数学符号与推导

### 3.1 CTL* 模型检测复杂度

| 逻辑 | 模型检测复杂度 | 可满足性复杂度 |
|------|--------------|--------------|
| CTL | $O(|M| \cdot |\phi|)$ | EXPTIME-完全 |
| LTL | PSPACE-完全 | PSPACE-完全 |
| CTL* | PSPACE-完全 | 2EXPTIME-完全 |

### 3.2 公平 CTL 的不动点

$$\mathbf{E}_f \mathbf{G} \phi = \nu Z. (\phi \wedge \bigwedge_{J \in \mathcal{J}} \mathbf{E}\mathbf{X}\mathbf{E}[\phi \mathbf{U} (Z \wedge J)])$$

---

## 四、示例性代码

```rust
/// 简化的 OBDD 节点（用于符号模型检测概念演示）
#[derive(Debug, Clone, PartialEq, Eq, Hash)]
pub enum Obdd {
    True,
    False,
    Node { var: usize, low: Box<Obdd>, high: Box<Obdd> },
}

impl Obdd {
    pub fn and(&self, other: &Obdd) -> Obdd {
        match (self, other) {
            (Obdd::False, _) | (_, Obdd::False) => Obdd::False,
            (Obdd::True, b) => b.clone(),
            (a, Obdd::True) => a.clone(),
            (Obdd::Node { var: v1, low: l1, high: h1 }, Obdd::Node { var: v2, low: l2, high: h2 }) => {
                if v1 == v2 {
                    Obdd::Node { var: *v1, low: Box::new(l1.and(l2)), high: Box::new(h1.and(h2)) }
                } else if v1 < v2 {
                    Obdd::Node { var: *v1, low: Box::new(l1.and(other)), high: Box::new(h1.and(other)) }
                } else {
                    Obdd::Node { var: *v2, low: Box::new(self.and(l2)), high: Box::new(self.and(h2)) }
                }
            }
        }
    }
}
```

---

## 五、形式化证明

### 5.1 CTL* 与交替树自动机等价性

**定理 5.1** 对任意 CTL* 公式 $\phi$，存在交替树自动机 $\mathcal{A}_\phi$ 使得 $M \models \phi$ 当且仅当 $\mathcal{A}_\phi$ 接受 $M$ 的计算树。

---

## 六、引用来源

1. [Emerson1990] Emerson, E. A. (1990). "Temporal and Modal Logic." In *Handbook of Theoretical Computer Science*, Vol. B, 995–1072.
2. [Kupferman2000] Kupferman, O., Vardi, M. Y., & Wolper, P. (2000). "An Automata-Theoretic Approach to Branching-Time Model Checking." *JACM*, 47(2), 312–360.
3. [McMillan1993] McMillan, K. L. (1993). *Symbolic Model Checking*. Kluwer.
4. [Clarke1994] Clarke, E., Grumberg, O., & Long, D. (1994). "Model Checking and Abstraction." *TOPLAS*, 16(5), 1512–1542.
5. [Cousot1977] Cousot, P., & Cousot, R. (1977). "Abstract Interpretation: A Unified Lattice Model for Static Analysis." *POPL*, 238–252.
"""
    },
]

def main():
    for item in SUPPLEMENTS:
        path = Path(item["path"])
        path.parent.mkdir(parents=True, exist_ok=True)
        path.write_text(item["content"], encoding="utf-8")
        print(f"Created: {path}")

if __name__ == "__main__":
    main()
