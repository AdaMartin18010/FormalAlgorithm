#!/usr/bin/env python3
from pathlib import Path

SUPPLEMENTS = [
    # 07-计算模型 (5)
    {
        "path": "docs/07-计算模型/03-组合子逻辑-六维补充.md",
        "content": """---
title: 03-组合子逻辑-六维补充
category: 07-计算模型
concepts: ["组合子逻辑", "SK组合子", "不动点组合子", "λ演算消去"]
level: 中级
---

# 组合子逻辑 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Barendregt (1984) The Lambda Calculus; Smullyan (1985) To Mock a Mockingbird

---

## 一、规范定义深化

### 1.1 组合子逻辑的形式化定义

**定义 1.1 (组合子)** 组合子（Combinator）是λ演算中不含自由变元的项。组合子逻辑系统由基本组合子与组合规则构成。

**经典组合子**:
- **S**: $\lambda f g x. f x (g x)$ — 替换组合子
- **K**: $\lambda x y. x$ — 常量组合子
- **I**: $\lambda x. x$ — 恒等组合子（可由 S 和 K 定义：$I = S K K$）

**定理 1.1 (Schönfinkel 完备性)** 任何λ项都可由 S 和 K 组合子表达。

### 1.2 不动点组合子

**Y 组合子**: $Y = \lambda f. (\lambda x. f (x x)) (\lambda x. f (x x))$

**性质**: $Y f = f (Y f)$，使递归定义无需自引用。

---

## 二、模型设计深化

### 2.1 组合子逻辑与λ演算的等价性

**消去变换** $T: \Lambda \to \mathcal{CL}$:
- $T(x) = x$
- $T(M N) = T(M) T(N)$
- $T(\lambda x. M) = K T(M)$（若 $x \notin FV(M)$）
- $T(\lambda x. x) = I$
- $T(\lambda x. M N) = S (\lambda x. M) (\lambda x. N)$

**定理 2.1** $T$ 保持β等价：$M =_\beta N \Rightarrow T(M) =_{SK} T(N)$。

---

## 三、数学符号与推导

### 3.1 SK 组合子的 Church-Rosser 性质

**定理 3.1** SK 组合子系统满足 Church-Rosser 性质：若 $M \twoheadrightarrow N_1$ 且 $M \twoheadrightarrow N_2$，则存在 $P$ 使得 $N_1 \twoheadrightarrow P$ 且 $N_2 \twoheadrightarrow P$。

---

## 四、示例性代码

```rust
/// SK 组合子求值器
#[derive(Debug, Clone)]
pub enum SK {
    S, K, I,
    App(Box<SK>, Box<SK>),
}

impl SK {
    pub fn eval(&self) -> SK {
        match self {
            SK::App(f, x) => match f.eval() {
                SK::I => x.eval(),
                SK::K => SK::App(Box::new(SK::K), x.clone()),
                SK::App(Box::new(SK::K), y) => y.eval(),
                SK::S => SK::App(Box::new(SK::S), x.clone()),
                SK::App(Box::new(SK::S), f1) => SK::App(Box::new(SK::App(Box::new(SK::S), f1)), x.clone()),
                SK::App(Box::new(SK::App(Box::new(SK::S), f1)), g1) => {
                    SK::App(Box::new(SK::App(f1.clone(), x.clone())), Box::new(SK::App(g1.clone(), x.clone()))).eval()
                }
                other => SK::App(Box::new(other), x.clone()),
            },
            atom => atom.clone(),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_i_combinator() {
        let term = SK::App(Box::new(SK::I), Box::new(SK::K));
        assert!(matches!(term.eval(), SK::K));
    }
}
```

---

## 五、形式化证明

### 5.1 Y 组合子不动点性质的 Lean4 草图

```lean4
def Y : (α → α) → α := λ f => (λ x => f (x x)) (λ x => f (x x))
-- 注意：在简单类型λ演算中Y不可类型化，需在递归类型或untyped系统中使用
```

---

## 六、引用来源

1. [Barendregt1984] Barendregt, H. P. (1984). *The Lambda Calculus: Its Syntax and Semantics*. North-Holland.
2. [Schonfinke1924] Schönfinkel, M. (1924). "Über die Bausteine der mathematischen Logik." *Mathematische Annalen*, 92, 305–316.
3. [Curry1958] Curry, H. B., & Feys, R. (1958). *Combinatory Logic, Vol. I*. North-Holland.
4. [Smullyan1985] Smullyan, R. (1985). *To Mock a Mockingbird*. Knopf.
5. [Hindley1986] Hindley, J. R., & Seldin, J. P. (1986). *Introduction to Combinators and λ-Calculus*. Cambridge University Press.
"""
    },
    {
        "path": "docs/07-计算模型/05-量子计算模型-六维补充.md",
        "content": """---
title: 05-量子计算模型-六维补充
category: 07-计算模型
concepts: ["量子计算", "量子电路", "量子图灵机", "BPP", "BQP"]
level: 高级
---

# 量子计算模型 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Nielsen & Chuang (2010) Quantum Computation and Quantum Information

---

## 一、规范定义深化

### 1.1 量子计算的形式化定义

**定义 1.1 (量子比特)** 量子比特（qubit）是二维复希尔伯特空间 $\mathcal{H}_2 = \mathbb{C}^2$ 中的单位向量：
$$|\psi\rangle = \alpha|0\rangle + \beta|1\rangle, \quad |\alpha|^2 + |\beta|^2 = 1$$

**定义 1.2 (量子电路)** 量子电路 $C = (n, G)$ 由 $n$ 个量子比特和门序列 $G = (g_1, \ldots, g_m)$ 组成，其中每个门 $g_i$ 为作用于 $k$ 个量子比特的酉变换 $U \in U(2^k)$。

### 1.2 量子图灵机

**定义 1.3 (Deutsch 量子图灵机)** QTM 由 $(Q, \Sigma, \Gamma, \delta, q_0, q_{acc}, q_{rej})$ 定义，其中迁移函数 $\delta$ 输出叠加态：
$$\delta(q, \sigma) = \sum_{q', \sigma', d} \alpha_{q', \sigma', d} |q', \sigma', d\rangle$$

---

## 二、模型设计深化

### 2.1 量子电路模型 vs 经典电路

| 特性 | 经典电路 | 量子电路 |
|------|----------|----------|
| 状态空间 | $\{0,1\}^n$ | $\mathbb{C}^{2^n}$（叠加）|
| 门操作 | 布尔函数 | 酉变换 $U^\dagger U = I$ |
| 可复制性 | 可克隆 | 不可克隆定理 |
| 可逆性 | 不可逆（除 NOT） | 必须可逆 |

### 2.2 复杂度类 BQP

**定义 2.1** $BQP$（Bounded-error Quantum Polynomial time）包含所有可被多项式规模量子电路以 $\geq 2/3$ 概率正确判定的语言。

**关系**: $P \subseteq BPP \subseteq BQP \subseteq PSPACE$，且 $BQP \subseteq EXP$。

---

## 三、数学符号与推导

### 3.1 量子傅里叶变换

$$QFT|j\rangle = \frac{1}{\sqrt{N}} \sum_{k=0}^{N-1} e^{2\pi i j k / N} |k\rangle$$

**电路复杂度**: $O(n^2)$ 门，$n = \log N$。

### 3.2 Grover 搜索的振幅分析

设 $N = 2^n$，标记项数为 $M$。Grover 迭代算子 $G = (2|\psi\rangle\langle\psi| - I) O$，其中 $O$ 为 Oracle。

经过 $R = \frac{\pi}{4} \sqrt{N/M}$ 次迭代，测量到解的概率 $\geq 1 - M/N$。

---

## 四、示例性代码

```rust
/// 量子门矩阵模拟（概念演示）
pub type QMatrix = Vec<Vec<(f64, f64)>>; // (real, imag)

pub fn hadamard() -> QMatrix {
    let s = 1.0 / 2.0_f64.sqrt();
    vec![
        vec![(s, 0.0), (s, 0.0)],
        vec![(s, 0.0), (-s, 0.0)],
    ]
}

pub fn pauli_x() -> QMatrix {
    vec![
        vec![(0.0, 0.0), (1.0, 0.0)],
        vec![(1.0, 0.0), (0.0, 0.0)],
    ]
}

/// 矩阵乘法（复数）
pub fn mat_mul(a: &QMatrix, b: &QMatrix) -> QMatrix {
    let n = a.len();
    let mut res = vec![vec![(0.0, 0.0); n]; n];
    for i in 0..n {
        for k in 0..n {
            for j in 0..n {
                let (ar, ai) = a[i][k];
                let (br, bi) = b[k][j];
                res[i][j].0 += ar * br - ai * bi;
                res[i][j].1 += ar * bi + ai * br;
            }
        }
    }
    res
}
```

---

## 五、形式化证明

### 5.1 不可克隆定理

**定理 5.1** 不存在通用量子克隆算子 $U$ 使得 $U|\psi\rangle|0\rangle = |\psi\rangle|\psi\rangle$ 对所有 $|\psi\rangle$ 成立。

*证明*: 若存在，则 $U$ 必须保持内积。但对 $|\psi\rangle \neq |\phi\rangle$：
$$\langle\psi|\phi\rangle = (\langle\psi|\langle0|)(|\phi\rangle|0\rangle) = (\langle\psi|\langle\psi|)(|\phi\rangle|\phi\rangle) = \langle\psi|\phi\rangle^2$$
这要求 $\langle\psi|\phi\rangle \in \{0, 1\}$，矛盾。

---

## 六、引用来源

1. [Nielsen2010] Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information* (10th Anniversary ed.). Cambridge.
2. [Deutsch1985] Deutsch, D. (1985). "Quantum Theory, the Church-Turing Principle and the Universal Quantum Computer." *Proceedings of the Royal Society A*, 400, 97–117.
3. [Shor1994] Shor, P. W. (1994). "Algorithms for Quantum Computation." *FOCS*, 124–134.
4. [Grover1996] Grover, L. K. (1996). "A Fast Quantum Mechanical Algorithm for Database Search." *STOC*, 212–219.
5. [Bernstein1997] Bernstein, E., & Vazirani, U. (1997). "Quantum Complexity Theory." *SIAM Journal on Computing*, 26(5), 1411–1473.
"""
    },
    {
        "path": "docs/07-计算模型/06-细胞自动机理论-六维补充.md",
        "content": """---
title: 06-细胞自动机理论-六维补充
category: 07-计算模型
concepts: ["细胞自动机", "元胞自动机", "Rule110", "Wolfram类", "可逆CA"]
level: 中级
---

# 细胞自动机理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Wolfram (2002) A New Kind of Science; Toffoli & Margolus (1987) Cellular Automata Machines

---

## 一、规范定义深化

### 1.1 细胞自动机的形式化定义

**定义 1.1 (细胞自动机)** 一维细胞自动机（CA）由四元组 $(S, r, d, f)$ 定义：
- **状态集 $S$**: 有限集合，通常 $|S| = k$
- **半径 $r$**: 邻居范围为 $[-r, r]$
- **维度 $d$**: 空间维度（$d=1, 2, \ldots$）
- **局部规则 $f: S^{2r+1} \to S$**: 状态更新函数

全局迁移函数 $F: S^{\mathbb{Z}^d} \to S^{\mathbb{Z}^d}$ 定义为：
$$F(c)_i = f(c_{i-r}, \ldots, c_{i+r})$$

### 1.2 Wolfram 分类

Wolfram 将一维 CA 分为四类：
1. **类 I**: 演化至均匀稳态
2. **类 II**: 演化至周期性模式
3. **类 III**: 混沌、随机行为
4. **类 IV**: 复杂、局部结构，可支持通用计算

**定理 1.1 (Cook)** Rule 110 是图灵完备的。

---

## 二、模型设计深化

### 2.1 可逆细胞自动机

**定义 2.1** CA $F$ 是可逆的，若存在逆 CA $F^{-1}$ 使得 $F^{-1} \circ F = id$。

**定理 2.1** 一维 CA 的可逆性是可判定的，但二维 CA 的可逆性不可判定。

### 2.2 分区细胞自动机 (Partitioned CA)

用于设计可逆 CA：每个细胞划分为多个子状态，更新时先交换子状态再应用局部规则。

---

## 三、数学符号与推导

### 3.1 Rule 110 的局部规则

状态集 $S = \{0, 1\}$，半径 $r = 1$，规则编号 110（二进制 $01101110$）：

| 邻居 $(L, C, R)$ | 111 | 110 | 101 | 100 | 011 | 010 | 001 | 000 |
|-------------------|-----|-----|-----|-----|-----|-----|-----|-----|
| 新状态 | 0 | 1 | 1 | 0 | 1 | 1 | 1 | 0 |

---

## 四、示例性代码

```rust
/// 一维细胞自动机模拟器
pub struct CellularAutomaton {
    rule: [u8; 8], // 8种邻居配置对应的输出
    state: Vec<u8>,
}

impl CellularAutomaton {
    pub fn new(rule_number: u8, initial_state: Vec<u8>) -> Self {
        let mut rule = [0u8; 8];
        for i in 0..8 {
            rule[i] = (rule_number >> i) & 1;
        }
        Self { rule, state: initial_state }
    }

    pub fn step(&mut self) {
        let n = self.state.len();
        let mut next = vec![0u8; n];
        for i in 0..n {
            let left = self.state[(i + n - 1) % n];
            let center = self.state[i];
            let right = self.state[(i + 1) % n];
            let idx = (left << 2 | center << 1 | right) as usize;
            next[i] = self.rule[idx];
        }
        self.state = next;
    }

    pub fn run(&mut self, steps: usize) -> Vec<Vec<u8>> {
        let mut history = vec![self.state.clone()];
        for _ in 0..steps {
            self.step();
            history.push(self.state.clone());
        }
        history
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rule_110() {
        let mut ca = CellularAutomaton::new(110, vec![0, 0, 0, 1, 0, 0, 0]);
        let history = ca.run(4);
        assert_eq!(history[0], vec![0, 0, 0, 1, 0, 0, 0]);
    }
}
```

---

## 五、形式化证明

### 5.1 一维 CA 可逆性的判定

**定理 5.1** 一维 CA 可逆当且仅当其全局映射是双射，这等价于所有有限配置的映射是单射。

**算法** (Amoroso & Patt): 检查所有长度为 $2r(2r+1)$ 的有限配置是否满足单射性。

---

## 六、引用来源

1. [Wolfram2002] Wolfram, S. (2002). *A New Kind of Science*. Wolfram Media.
2. [Toffoli1987] Toffoli, T., & Margolus, N. (1987). *Cellular Automata Machines*. MIT Press.
3. [Cook2004] Cook, M. (2004). "Universality in Elementary Cellular Automata." *Complex Systems*, 15(1), 1–40.
4. [Amoroso1972] Amoroso, S., & Patt, Y. N. (1972). "Decision Procedures for Surjectivity and Injectivity of Parallel Maps for Tessellation Structures." *JCSS*, 6(5), 448–464.
5. [Kari2005] Kari, J. (2005). "Theory of Cellular Automata: A Survey." *Theoretical Computer Science*, 334(1–3), 3–33.
"""
    },
    {
        "path": "docs/07-计算模型/07-神经网络计算模型-六维补充.md",
        "content": """---
title: 07-神经网络计算模型-六维补充
category: 07-计算模型
concepts: ["神经网络", "计算模型", "RNN", "图灵机", "通用逼近定理"]
level: 中级
---

# 神经网络计算模型 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Siegelmann & Sontag (1995) On the Computational Power of Neural Nets; Goodfellow et al. (2016) Deep Learning

---

## 一、规范定义深化

### 1.1 神经网络的形式化定义

**定义 1.1 (前馈神经网络)** 前馈神经网络 $N = (L, (W^{(l)}, b^{(l)})_{l=1}^L, \sigma)$ 由：
- **层数 $L$**: 隐藏层数 + 输出层
- **权重矩阵 $W^{(l)} \in \mathbb{R}^{n_l \times n_{l-1}}$**
- **偏置向量 $b^{(l)} \in \mathbb{R}^{n_l}$**
- **激活函数 $\sigma$**: 逐元素非线性函数

定义。前向传播：
$$a^{(0)} = x, \quad z^{(l)} = W^{(l)} a^{(l-1)} + b^{(l)}, \quad a^{(l)} = \sigma(z^{(l)})$$

### 1.2 循环神经网络 (RNN)

**定义 1.2** RNN 维护隐藏状态 $h_t$，按序处理输入：
$$h_t = \sigma(W_h h_{t-1} + W_x x_t + b)$$

---

## 二、模型设计深化

### 2.1 通用逼近定理

**定理 2.1 (Cybenko 1989; Hornik 1991)** 具有至少一个隐藏层、有限个神经元和非常数连续激活函数的前馈神经网络，可以在紧集上以任意精度逼近任意连续函数。

**形式化**: 对任意 $\epsilon > 0$，紧集 $K \subset \mathbb{R}^d$，连续函数 $f: K \to \mathbb{R}$，存在神经网络 $N$ 使得：
$$\sup_{x \in K} |f(x) - N(x)| < \epsilon$$

### 2.2 神经网络的图灵完备性

**定理 2.2 (Siegelmann & Sontag 1995)** 使用饱和线性激活函数（如 ReLU）和有理数权重的 RNN 可以模拟任意图灵机。

**关键条件**: 无限精度权重 + 无限运行时间。

---

## 三、数学符号与推导

### 3.1 反向传播的梯度推导

损失函数 $J$ 对 $W^{(l)}$ 的梯度：
$$\frac{\partial J}{\partial W^{(l)}} = \delta^{(l)} (a^{(l-1)})^T$$

其中误差项：
$$\delta^{(l)} = ((W^{(l+1)})^T \delta^{(l+1)}) \odot \sigma'(z^{(l)})$$

### 3.2 Transformer 的自注意力复杂度

$$Attention(Q, K, V) = softmax\left(\frac{QK^T}{\sqrt{d_k}}\right) V$$

时间复杂度: $O(n^2 \cdot d)$（$n$ 序列长度，$d$ 维度）

---

## 四、示例性代码

```rust
/// 前馈神经网络前向传播（简化版）
pub struct FNN {
    weights: Vec<Vec<Vec<f64>>>, // layer x output x input
    biases: Vec<Vec<f64>>,       // layer x output
}

impl FNN {
    pub fn forward(&self, input: &[f64]) -> Vec<f64> {
        let mut a = input.to_vec();
        for (w, b) in self.weights.iter().zip(&self.biases) {
            let mut z = vec![0.0; b.len()];
            for i in 0..b.len() {
                z[i] = b[i];
                for j in 0..a.len() {
                    z[i] += w[i][j] * a[j];
                }
            }
            // ReLU activation
            a = z.iter().map(|&x| x.max(0.0)).collect();
        }
        a
    }
}
```

---

## 五、形式化证明

### 5.1 通用逼近定理的证明框架

*证明概要* (Cybenko):
1. 证明单隐藏层网络可表示的函数集合在 $C(K)$ 中稠密
2. 使用 Hahn-Banach 定理：若泛函 $L$ 在所有神经网络输出上为零，则 $L = 0$
3. 利用 Fourier 变换证明不存在非零此类泛函

---

## 六、引用来源

1. [Siegelmann1995] Siegelmann, H. T., & Sontag, E. D. (1995). "On the Computational Power of Neural Nets." *JCSS*, 50(1), 132–150.
2. [Cybenko1989] Cybenko, G. (1989). "Approximation by Superpositions of a Sigmoidal Function." *Mathematics of Control, Signals, and Systems*, 2(4), 303–314.
3. [Hornik1991] Hornik, K. (1991). "Approximation Capabilities of Multilayer Feedforward Networks." *Neural Networks*, 4(2), 251–257.
4. [Goodfellow2016] Goodfellow, I., Bengio, Y., & Courville, A. (2016). *Deep Learning*. MIT Press.
5. [Vaswani2017] Vaswani, A., et al. (2017). "Attention Is All You Need." *NeurIPS*, 5998–6008.
"""
    },
    {
        "path": "docs/07-计算模型/08-计算模型等价性理论-六维补充.md",
        "content": """---
title: 08-计算模型等价性理论-六维补充
category: 07-计算模型
concepts: ["Church-Turing论题", "计算模型等价性", "模拟", "归约", "图灵完备"]
level: 中级
---

# 计算模型等价性理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Sipser (2013) Introduction to the Theory of Computation; Rogers (1967) Theory of Recursive Functions and Effective Computability

---

## 一、规范定义深化

### 1.1 Church-Turing 论题

**论题 1.1 (Church-Turing)** 所有"直观可计算"的函数都可被图灵机计算。

**强 Church-Turing 论题**: 任何物理过程都可被概率图灵机以多项式开销模拟。

**扩展 (Deutsch 1985)**: 量子图灵机可以模拟任何有限量子力学系统。

### 1.2 计算模型等价的形式化定义

**定义 1.2 (模拟)** 计算模型 $M_1$ 模拟 $M_2$，若存在编码 $e$ 和解码 $d$，使得对 $M_2$ 的任何计算 $C_2$，$M_1$ 存在计算 $C_1$ 满足 $d(C_1) = C_2$。

**定义 1.3 (多项式时间模拟)** 若模拟的时空开销为多项式，则称 $M_1$ 多项式模拟 $M_2$。

---

## 二、模型设计深化

### 2.1 主要计算模型的等价关系

| 模型 | 确定性版本 | 非确定性版本 | 概率版本 |
|------|-----------|-------------|---------|
| 图灵机 | TM | NTM | PTM |
| λ演算 | λ | — | — |
| 递归函数 | 部分递归 | — | — |
| 寄存器机 | RAM | NRAM | — |
| 细胞自动机 | DCA | — | — |
| 量子电路 | — | — | QC |

**定理 2.1** 图灵机、λ演算、部分递归函数、RAM 在计算能力上等价（可互相模拟）。

---

## 三、数学符号与推导

### 3.1 图灵机模拟 RAM

**定理 3.1** 任何 $T(n)$ 时间的 RAM 可被图灵机在 $O(T(n)^3)$ 时间内模拟。

*证明概要*:
1. RAM 寄存器内容存储在图灵机磁带上的地址-值对列表
2. 每次 RAM 指令执行需扫描磁带查找操作数
3. 若 RAM 使用 $S(n)$ 空间，则地址最大为 $S(n)$，编码长度为 $O(\log S(n))$
4. 总时间开销为 $O(T(n) \cdot S(n) \cdot \log S(n))$，对于标准 RAM 为 $O(T(n)^2)$

### 3.2 量子电路模拟经典电路

**定理 3.2** 任何经典电路 $C$ 可被量子电路以相同门数模拟（使用 Toffoli 门和 Hadamard 门）。

---

## 四、示例性代码

```rust
/// 通用图灵机模拟器框架（概念演示）
pub struct TuringMachine {
    states: Vec<String>,
    alphabet: Vec<char>,
    transitions: std::collections::HashMap<(String, char), (String, char, i8)>,
    tape: Vec<char>,
    head: isize,
    state: String,
}

impl TuringMachine {
    pub fn step(&mut self) -> bool {
        let symbol = self.tape.get(self.head as usize).copied().unwrap_or('_');
        match self.transitions.get(&(self.state.clone(), symbol)) {
            Some((new_state, new_symbol, move_dir)) => {
                if self.head >= 0 && (self.head as usize) < self.tape.len() {
                    self.tape[self.head as usize] = *new_symbol;
                }
                self.head += *move_dir as isize;
                self.state = new_state.clone();
                true
            }
            None => false,
        }
    }
}
```

---

## 五、形式化证明

### 5.1 图灵机与 λ 演算的等价性

**定理 5.1** 部分递归函数类 = 图灵可计算函数类 = λ 可定义函数类。

*证明框架*:
1. **λ → TM**: 通过消去变换将 λ 项编译为组合子，再模拟组合子归约
2. **TM → λ**: 将图灵机配置编码为 Church 数对，迁移函数编码为 λ 项
3. **TM → 递归函数**: 使用 Gödel 编号和原始递归定义图灵机的一步迁移函数

---

## 六、引用来源

1. [Sipser2013] Sipser, M. (2013). *Introduction to the Theory of Computation* (3rd ed.). Cengage Learning.
2. [Rogers1967] Rogers, H. (1967). *Theory of Recursive Functions and Effective Computability*. McGraw-Hill.
3. [Deutsch1985] Deutsch, D. (1985). "Quantum Theory, the Church-Turing Principle and the Universal Quantum Computer." *Proceedings of the Royal Society A*, 400, 97–117.
4. [vanEmdeBoas1990] van Emde Boas, P. (1990). "Machine Models and Simulations." In *Handbook of Theoretical Computer Science*, Vol. A, 1–66.
5. [Copeland2002] Copeland, B. J. (2002). "The Church-Turing Thesis." In *Stanford Encyclopedia of Philosophy*.
"""
    },
    # 09-算法理论 (4)
    {
        "path": "docs/09-算法理论/01-算法基础/10-分支限界算法理论-六维补充.md",
        "content": """---
title: 10-分支限界算法理论-六维补充
category: 09-算法理论
concepts: ["分支限界", "状态空间树", "上界", "下界", "剪枝"]
level: 基础
---

# 分支限界算法理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: CLRS 第4版分支限界 [CLRS2022]; Lawler & Wood (1966) Branch-and-Bound Methods

---

## 一、规范定义深化

### 1.1 分支限界的形式化定义

**定义 1.1 (分支限界)** 分支限界（Branch and Bound, B&B）是一种系统性地搜索组合优化问题解空间的策略，由以下要素构成：

- **分支 (Branching)**: 将问题分解为子问题（通常通过决策变量取值）
- **限界 (Bounding)**: 计算子问题的上界/下界，以评估该子问题是否可能包含最优解
- **剪枝 (Pruning)**: 若子问题的界不优于当前最优解，则舍弃该子问题

**定义 1.2 (界函数)** 对最小化问题，下界函数 $LB(P)$ 满足 $LB(P) \leq OPT(P)$；对最大化问题，上界函数 $UB(P)$ 满足 $UB(P) \geq OPT(P)$。

---

## 二、模型设计深化

### 2.1 搜索策略

| 策略 | 选择规则 | 空间复杂度 | 适用场景 |
|------|----------|-----------|----------|
| FIFO (队列) | 先进先出 | $O(b^d)$ | 广度优先风格 |
| LIFO (栈) | 后进先出 | $O(bd)$ | 深度优先风格 |
| LC (最小耗费) | $min LB(P_i)$ | $O(b^d)$ | 最快收敛到最优 |

其中 $b$ 为分支因子，$d$ 为解深度。

### 2.2 松弛技术

**线性规划松弛**: 将整数规划 $\min c^T x$ s.t. $Ax \leq b, x \in \mathbb{Z}^n$ 松弛为 $x \in \mathbb{R}^n$。

**定理 2.1** 线性规划松弛给出整数规划的最优下界。

---

## 三、数学符号与推导

### 3.1 0/1 背包问题的分支限界

**问题**: $\max \sum_{i=1}^n v_i x_i$，s.t. $\sum_{i=1}^n w_i x_i \leq W, x_i \in \{0,1\}$

**下界计算**（贪心松弛）: 按价值密度 $v_i/w_i$ 排序，对当前节点已固定的变量取定值，剩余变量按贪心填装。

**剪枝条件**: 若当前节点的上界 $\leq$ 已找到的最优值，则剪枝。

---

## 四、示例性代码

```rust
/// 0/1 背包问题 — 分支限界求解器
#[derive(Debug, Clone)]
pub struct Item {
    pub weight: usize,
    pub value: usize,
}

#[derive(Debug)]
pub struct KnapsackNode {
    level: usize,
    profit: usize,
    weight: usize,
    bound: f64,
}

pub fn knapsack_branch_bound(items: &[Item], capacity: usize) -> usize {
    let mut sorted = items.to_vec();
    sorted.sort_by(|a, b| {
        let ra = a.value as f64 / a.weight as f64;
        let rb = b.value as f64 / b.weight as f64;
        rb.partial_cmp(&ra).unwrap()
    });

    let mut max_profit = 0usize;
    let mut stack = vec![KnapsackNode { level: 0, profit: 0, weight: 0, bound: bound(&sorted, capacity, 0, 0, 0) }];

    while let Some(node) = stack.pop() {
        if node.bound <= max_profit as f64 || node.level >= sorted.len() {
            continue;
        }
        let item = &sorted[node.level];
        // 包含当前物品
        if node.weight + item.weight <= capacity {
            let profit = node.profit + item.value;
            max_profit = max_profit.max(profit);
            let b = bound(&sorted, capacity, node.level + 1, profit, node.weight + item.weight);
            stack.push(KnapsackNode { level: node.level + 1, profit, weight: node.weight + item.weight, bound: b });
        }
        // 不包含当前物品
        let b = bound(&sorted, capacity, node.level + 1, node.profit, node.weight);
        stack.push(KnapsackNode { level: node.level + 1, profit: node.profit, weight: node.weight, bound: b });
    }
    max_profit
}

fn bound(items: &[Item], capacity: usize, level: usize, profit: usize, weight: usize) -> f64 {
    if weight >= capacity { return 0.0; }
    let mut bound = profit as f64;
    let mut w = weight;
    for i in level..items.len() {
        if w + items[i].weight <= capacity {
            w += items[i].weight;
            bound += items[i].value as f64;
        } else {
            bound += (capacity - w) as f64 * items[i].value as f64 / items[i].weight as f64;
            break;
        }
    }
    bound
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_knapsack_bb() {
        let items = vec![
            Item { weight: 10, value: 60 },
            Item { weight: 20, value: 100 },
            Item { weight: 30, value: 120 },
        ];
        assert_eq!(knapsack_branch_bound(&items, 50), 220);
    }
}
```

---

## 五、形式化证明

### 5.1 分支限界的完备性

**定理 5.1** 若界函数 $LB$ 满足 $LB(P) \leq OPT(P)$ 且搜索空间有限，则分支限界算法必在有限步内找到最优解。

*证明*: 
1. 有限搜索空间保证算法终止
2. 剪枝仅丢弃界不优于当前最优的子问题
3. 最优解所在子问题的界 $\geq OPT$，不会被剪枝
4. 因此最优解必被访问

---

## 六、引用来源

1. [CLRS2022] Cormen, T. H., et al. (2022). *Introduction to Algorithms* (4th ed.). MIT Press.
2. [Lawler1966] Lawler, E. L., & Wood, D. E. (1966). "Branch-and-Bound Methods: A Survey." *Operations Research*, 14(4), 699–719.
3. [Land1960] Land, A. H., & Doig, A. G. (1960). "An Automatic Method of Solving Discrete Programming Problems." *Econometrica*, 28(3), 497–520.
4. [Little1963] Little, J. D. C., et al. (1963). "An Algorithm for the Traveling Salesman Problem." *Operations Research*, 11(6), 972–989.
5. [Morrison2016] Morrison, D. R., et al. (2016). "Branch-and-Bound Algorithms: A Survey of Recent Advances in Searching, Branching, and Pruning." *Discrete Optimization*, 19, 79–102.
"""
    },
    {
        "path": "docs/09-算法理论/01-算法基础/11-随机算法理论-六维补充.md",
        "content": """---
title: 11-随机算法理论-六维补充
category: 09-算法理论
concepts: ["随机算法", "Las Vegas", "Monte Carlo", "概率分析", "指示器随机变量"]
level: 基础
---

# 随机算法理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: CLRS 第4版随机算法 [CLRS2022]; Motwani & Raghavan (1995) Randomized Algorithms

---

## 一、规范定义深化

### 1.1 随机算法的分类

**定义 1.1 (Las Vegas 算法)** 总是输出正确结果，但运行时间是随机变量。对任意输入 $x$：
$$P[\text{Algorithm}(x) \text{ is correct}] = 1$$

**定义 1.2 (Monte Carlo 算法)** 运行时间是确定的（或有界的），但输出以一定概率错误。
- **单侧错误**: $P[\text{error}] \leq \epsilon$ 且错误方向固定
- **双侧错误**: $P[\text{error}] \leq \epsilon$ 且错误方向不固定

### 1.2 期望复杂度

**定义 1.3** 随机算法 $A$ 的期望时间复杂度：
$$E[T_A(n)] = \max_{|x|=n} E[T_A(x)]$$

---

## 二、模型设计深化

### 2.1 概率图灵机

**定义 2.1 (概率图灵机, PTM)** PTM 在每个步骤有两个可能的迁移，各以概率 $1/2$ 选择。

**复杂度类**:
- **$RP$**: 单侧错误多项式时间（若 $x \in L$ 则 $P[\text{accept}] \geq 1/2$；若 $x \notin L$ 则 $P[\text{accept}] = 0$）
- **$BPP$**: 双侧错误多项式时间（$P[\text{correct}] \geq 2/3$）
- **$ZPP$**: 零错误期望多项式时间（$ZPP = RP \cap coRP$）

**关系**: $P \subseteq ZPP \subseteq RP \subseteq BPP \subseteq PSPACE$

---

## 三、数学符号与推导

### 3.1 快速排序的期望分析

设 $X$ 为总比较次数，$X_{ij} = \mathbb{1}\{z_i \text{ 与 } z_j \text{ 被比较}\}$。

$z_i$ 与 $z_j$ 被比较当且仅当在 $\{z_i, \ldots, z_j\}$ 中 $z_i$ 或 $z_j$ 率先被选为枢轴：
$$P[X_{ij} = 1] = \frac{2}{j-i+1}$$

期望：
$$E[X] = \sum_{i=1}^{n-1}\sum_{j=i+1}^n \frac{2}{j-i+1} = O(n \log n)$$

### 3.2 随机化最小割 (Karger 算法)

**定理 3.1** Karger 随机收缩算法以概率 $\geq 2/(n(n-1))$ 找到全局最小割。

**重复增强**: 独立运行 $O(n^2 \log n)$ 次，失败概率 $\leq (1 - 2/n^2)^{cn^2 \log n} \leq n^{-c'}$。

---

## 四、示例性代码

```rust
use rand::seq::SliceRandom;
use rand::thread_rng;

/// 随机化快速排序
pub fn randomized_quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 { return; }
    arr.shuffle(&mut thread_rng());
    let pivot = partition(arr);
    randomized_quick_sort(&mut arr[..pivot]);
    randomized_quick_sort(&mut arr[pivot + 1..]);
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let n = arr.len();
    let mut i = 0;
    for j in 0..n - 1 {
        if arr[j] <= arr[n - 1] {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, n - 1);
    i
}

/// 随机选择 (QuickSelect) — 期望 O(n)
pub fn randomized_select<T: Ord>(arr: &mut [T], k: usize) -> &T {
    if arr.len() == 1 { return &arr[0]; }
    arr.shuffle(&mut thread_rng());
    let pivot = partition(arr);
    match k.cmp(&pivot) {
        std::cmp::Ordering::Equal => &arr[pivot],
        std::cmp::Ordering::Less => randomized_select(&mut arr[..pivot], k),
        std::cmp::Ordering::Greater => randomized_select(&mut arr[pivot + 1..], k - pivot - 1),
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_randomized_quick_sort() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        randomized_quick_sort(&mut arr);
        assert!(arr.windows(2).all(|w| w[0] <= w[1]));
    }

    #[test]
    fn test_randomized_select() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        let median = randomized_select(&mut arr.clone(), 3);
        assert_eq!(*median, 25);
    }
}
```

---

## 五、形式化证明

### 5.1 Karger 算法成功概率的下界

**定理 5.1** Karger 随机边收缩找到最小割的概率至少为 $2/(n(n-1))$。

*证明*:
设最小割大小为 $k$，则最小度 $\geq k$，边数 $m \geq kn/2$。

第 $i$ 步（剩余 $n-i+1$ 个顶点）收缩最小割边的概率：
$$P_i \leq \frac{k}{m_i} \leq \frac{k}{k(n-i+1)/2} = \frac{2}{n-i+1}$$

最小割在所有 $n-2$ 步中均未被收缩的概率：
$$\prod_{i=1}^{n-2} \left(1 - \frac{2}{n-i+1}\right) = \prod_{j=3}^{n} \frac{j-2}{j} = \frac{2}{n(n-1)}$$

---

## 六、引用来源

1. [CLRS2022] Cormen, T. H., et al. (2022). *Introduction to Algorithms* (4th ed.). MIT Press.
2. [Motwani1995] Motwani, R., & Raghavan, P. (1995). *Randomized Algorithms*. Cambridge University Press.
3. [Karger1993] Karger, D. R. (1993). "Global Min-cuts in RNC, and Other Ramifications of a Simple Min-Cut Algorithm." *SODA*, 21–30.
4. [Rabin1980] Rabin, M. O. (1980). "Probabilistic Algorithm for Testing Primality." *Journal of Number Theory*, 12(1), 128–138.
5. [Schwartz1980] Schwartz, J. T. (1980). "Fast Probabilistic Algorithms for Verification of Polynomial Identities." *JACM*, 27(4), 701–717.
"""
    },
    {
        "path": "docs/09-算法理论/01-算法基础/12-近似算法理论-六维补充.md",
        "content": """---
title: 12-近似算法理论-六维补充
category: 09-算法理论
concepts: ["近似算法", "近似比", "PTAS", "FPTAS", "不可近似性"]
level: 中级
---

# 近似算法理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Vazirani (2001) Approximation Algorithms; Williamson & Shmoys (2011) The Design of Approximation Algorithms

---

## 一、规范定义深化

### 1.1 近似算法的形式化定义

**定义 1.1 (近似比)** 对最小化问题，算法 $A$ 的近似比 $\rho(n) \geq 1$ 满足：
$$\frac{A(I)}{OPT(I)} \leq \rho(n)$$

对最大化问题：
$$\frac{OPT(I)}{A(I)} \leq \rho(n)$$

**定义 1.2 (PTAS)** 多项式时间近似方案（PTAS）对任意固定 $\epsilon > 0$ 给出 $(1+\epsilon)$-近似算法，运行时间为 $O(n^{f(1/\epsilon)})$。

**定义 1.3 (FPTAS)** 完全多项式时间近似方案（FPTAS）的运行时间为 $poly(n, 1/\epsilon)$。

---

## 二、模型设计深化

### 2.1 近似难度层次

| 近似类型 | 定义 | 典型问题 |
|----------|------|----------|
| 常数近似 | $\rho = O(1)$ | 顶点覆盖、Steiner 树 |
| 对数近似 | $\rho = O(\log n)$ | 集合覆盖、连通支配集 |
| 多项式近似 | $\rho = O(n^\epsilon)$ | 图着色、最大团 |
| PTAS | $(1+\epsilon)$-近似 | 欧几里得 TSP、背包 |
| APX-hard | 不存在 PTAS（$P \neq NP$） | MAX-3SAT、度量 TSP |

### 2.2 PCP 定理与不可近似性

**定理 2.1 (PCP 定理)** $NP = PCP[O(\log n), O(1)]$。

**推论**: 若 $P \neq NP$，则 MAX-3SAT 不存在 $(8/7 - \epsilon)$-近似算法。

---

## 三、数学符号与推导

### 3.1 集合覆盖的贪心近似

**问题**: 给定集合族 $\mathcal{S} = \{S_1, \ldots, S_m\}$ 覆盖全集 $U$，求最小子族覆盖 $U$。

**贪心算法**: 每次选择覆盖最多未覆盖元素的集合。

**定理 3.1** 贪心集合覆盖是 $H_n$-近似的，其中 $H_n = \sum_{i=1}^n 1/i \approx \ln n$。

*证明*（收费论证）:
对元素 $e$，设其在第 $i$ 步被覆盖，此时剩余 $k_i$ 个未覆盖元素。为 $e$ 收费 $1/k_i$。

总收费 = 算法解大小。每个集合 $S_j^*$ 在最优解中，其元素总收费 $\leq H_{|S_j^*|} \leq H_n$。

因此 $ALG = \sum_e charge(e) \leq H_n \cdot OPT$。

### 3.2 度量 TSP 的 Christofides 算法

**算法**:
1. 构造最小生成树 $T$
2. 找到 $T$ 中奇度顶点的最小权完美匹配 $M$
3. $T + M$ 为欧拉图，找欧拉回路后 shortcut 得哈密顿回路

**定理 3.2** Christofides 算法是 $3/2$-近似的。

---

## 四、示例性代码

```rust
/// 顶点覆盖的 2-近似贪心算法
use std::collections::HashSet;

pub fn vertex_cover_2approx(edges: &[(usize, usize)]) -> HashSet<usize> {
    let mut cover = HashSet::new();
    let mut remaining: Vec<(usize, usize)> = edges.to_vec();

    while let Some((u, v)) = remaining.pop() {
        if cover.contains(&u) || cover.contains(&v) {
            continue;
        }
        cover.insert(u);
        cover.insert(v);
        remaining.retain(|&(a, b)| !cover.contains(&a) && !cover.contains(&b));
    }
    cover
}

/// 集合覆盖的贪心近似算法
pub fn set_cover_greedy<'a>(universe: &[usize], sets: &'a [HashSet<usize>]) -> Vec<usize> {
    let mut uncovered: HashSet<usize> = universe.iter().copied().collect();
    let mut selected = Vec::new();

    while !uncovered.is_empty() {
        let (best_idx, best_cov) = sets.iter().enumerate()
            .map(|(i, s)| (i, s.intersection(&uncovered).count()))
            .max_by_key(|&(_, c)| c)
            .unwrap();
        if best_cov == 0 { break; }
        selected.push(best_idx);
        uncovered.retain(|e| !sets[best_idx].contains(e));
    }
    selected
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_vertex_cover() {
        let edges = vec![(0,1),(1,2),(2,3),(3,0),(0,2)];
        let cover = vertex_cover_2approx(&edges);
        for (u, v) in &edges {
            assert!(cover.contains(u) || cover.contains(v));
        }
    }
}
```

---

## 五、形式化证明

### 5.1 Christofides 算法的近似比

**定理 5.1** Christofides 算法输出的 TSP 回路长度 $C$ 满足 $C \leq \frac{3}{2} OPT$。

*证明*:
1. $c(T) \leq OPT$（删除 TSP 最优回路的一条边得生成树）
2. 设 $V_{odd}$ 为 $T$ 的奇度顶点，$|V_{odd}|$ 为偶数
3. $OPT$ 在 $V_{odd}$ 上的 shortcut 回路可分解为两个完美匹配，故 $c(M) \leq \frac{1}{2} OPT_{V_{odd}} \leq \frac{1}{2} OPT$
4. 欧拉回路 shortcut 不增加长度（三角不等式）
5. $C \leq c(T) + c(M) \leq OPT + \frac{1}{2}OPT = \frac{3}{2}OPT$

---

## 六、引用来源

1. [Vazirani2001] Vazirani, V. V. (2001). *Approximation Algorithms*. Springer.
2. [Williamson2011] Williamson, D. P., & Shmoys, D. B. (2011). *The Design of Approximation Algorithms*. Cambridge University Press.
3. [Christofides1976] Christofides, N. (1976). "Worst-Case Analysis of a New Heuristic for the Traveling Salesman Problem." *Report 388*, CMU.
4. [Arora1998] Arora, S. (1998). "Polynomial Time Approximation Schemes for Euclidean Traveling Salesman and Other Geometric Problems." *JACM*, 45(5), 753–782.
5. [Feige1998] Feige, U. (1998). "A Threshold of ln n for Approximating Set Cover." *JACM*, 45(4), 634–652.
"""
    },
    {
        "path": "docs/09-算法理论/01-算法基础/15-量子算法理论-六维补充.md",
        "content": """---
title: 15-量子算法理论-六维补充
category: 09-算法理论
concepts: ["量子算法", "Shor算法", "Grover算法", "HHL", "VQE"]
level: 高级
---

# 量子算法理论 — 六维补充

> **版本**: 1.0
> **创建日期**: 2026-04-20
> **对标**: Nielsen & Chuang (2010) Quantum Computation; Montanaro (2016) Quantum Algorithms

---

## 一、规范定义深化

### 1.1 量子查询模型

**定义 1.1 (量子查询复杂度)** 黑盒函数 $f: \{0,1\}^n \to \{0,1\}$ 的量子查询复杂度 $Q(f)$ 是计算 $f$ 所需的最少量子 Oracle 调用次数。

**量子 Oracle**: $O_f |x\rangle|y\rangle = |x\rangle|y \oplus f(x)\rangle$

### 1.2 主要量子算法

| 算法 | 问题 | 量子复杂度 | 经典复杂度 | 加速 |
|------|------|-----------|-----------|------|
| **Deutsch-Jozsa** | 判定 $f$ 是否常数或平衡 | $O(1)$ | $\Omega(2^n)$ | 指数 |
| **Grover** | 无序搜索 | $O(\sqrt{N})$ | $O(N)$ | 二次 |
| **Shor** | 整数分解 | $O((\log n)^3)$ | $O(\exp((\log n)^{1/3}))$ | 超多项式 |
| **HHL** | 线性系统 $Ax=b$ | $O(\log N \cdot \kappa^2)$ | $O(N \cdot \kappa)$ | 指数（条件数依赖）|
| **QAOA** | 组合优化 | 启发式 | — | 待验证 |

---

## 二、模型设计深化

### 2.1 量子相位估计 (QPE)

**目标**: 估计酉算子 $U$ 的特征值 $e^{2\pi i \varphi}$，其中 $U|\psi\rangle = e^{2\pi i \varphi}|\psi\rangle$。

**电路**: 使用 $t$ 个辅助量子比特，应用受控 $U^{2^k}$，然后逆 QFT。

**精度**: $t$ 个量子比特可估计 $\varphi$ 到 $t$ 位二进制精度。

### 2.2 HHL 算法

**问题**: 求解线性系统 $A\mathbf{x} = \mathbf{b}$，$A$ 为 $N \times N$ 厄米特矩阵。

**步骤**:
1. 状态准备：$|\mathbf{b}\rangle = \sum_i b_i |i\rangle$
2. QPE 估计 $A$ 的特征值 $\lambda_j$
3. 受控旋转：$|0\rangle \to \sqrt{1 - C^2/\lambda_j^2}|0\rangle + C/\lambda_j |1\rangle$
4. 逆 QPE，测量辅助比特为 1 时得解编码态

**复杂度**: $O(\log N \cdot \kappa^2 / \epsilon)$，其中 $\kappa = ||A|| \cdot ||A^{-1}||$ 为条件数。

---

## 三、数学符号与推导

### 3.1 Shor 算法的核心：阶寻找

**问题**: 给定 $a, N$ 互质，找最小 $r$ 使得 $a^r \equiv 1 \pmod{N}$。

**量子步骤**:
1. 制备叠加态 $\frac{1}{\sqrt{Q}} \sum_{x=0}^{Q-1} |x\rangle|0\rangle$
2. 模幂运算：$|x\rangle|a^x \mod N\rangle$
3. 测量第二寄存器，第一寄存器为周期函数的叠加
4. QPE 提取周期 $r$

**成功概率**: 对随机选取的 $a$，阶寻找成功概率 $\geq \frac{\varphi(N)}{N} \cdot \frac{1}{\log \log N}$，重复 $O(\log N)$ 次即可高概率成功。

### 3.2 Grover 几何解释

初始态 $|\psi\rangle = \cos\frac{\theta}{2} |\alpha\rangle + \sin\frac{\theta}{2} |\beta\rangle$，其中 $|\beta\rangle$ 为解子空间。

每次 Grover 迭代旋转 $2\theta$，其中 $\sin\frac{\theta}{2} = \sqrt{M/N}$。

最优迭代次数：$R = \frac{\pi}{4\theta} \approx \frac{\pi}{4}\sqrt{\frac{N}{M}}$。

---

## 四、示例性代码

```rust
/// 量子算法概念演示：Grover 振幅放大迭代
/// 注：此代码为经典模拟，展示算法逻辑而非量子执行

pub struct GroverSimulator {
    n: usize,
    marked: Vec<usize>,
    state: Vec<f64>, // 实振幅简化
}

impl GroverSimulator {
    pub fn new(n: usize, marked: Vec<usize>) -> Self {
        let n_states = 1usize << n;
        let amp = 1.0 / (n_states as f64).sqrt();
        Self { n, marked, state: vec![amp; n_states] }
    }

    pub fn oracle(&mut self) {
        for &m in &self.marked {
            self.state[m] = -self.state[m];
        }
    }

    pub fn diffusion(&mut self) {
        let n = self.state.len();
        let avg: f64 = self.state.iter().sum::<f64>() / n as f64;
        for s in &mut self.state {
            *s = 2.0 * avg - *s;
        }
    }

    pub fn iterate(&mut self) {
        self.oracle();
        self.diffusion();
    }

    pub fn probability(&self, idx: usize) -> f64 {
        self.state[idx].powi(2)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_grover() {
        let mut sim = GroverSimulator::new(4, vec![10]);
        let init_prob = sim.probability(10);
        sim.iterate();
        let after_prob = sim.probability(10);
        assert!(after_prob > init_prob);
    }
}
```

---

## 五、形式化证明

### 5.1 Grover 最优性

**定理 5.1 (BBHT)** 任何量子搜索算法对 $N$ 个元素中搜索 $M$ 个标记项，成功概率 $> 1/2$ 所需查询次数至少为 $\Omega(\sqrt{N/M})$。

*证明概要*（Bennett-Bernstein-Brassard-Vazirani）:
1. 将搜索问题转化为区分 Oracle $O_f$ 和恒等算子
2. 使用混合论证（hybrid argument）证明：经过 $T$ 次查询后，量子态与初始态的差异为 $O(T/\sqrt{N})$
3. 要区分标记态和均匀态需差异 $\Omega(1)$，故 $T = \Omega(\sqrt{N})$

---

## 六、引用来源

1. [Nielsen2010] Nielsen, M. A., & Chuang, I. L. (2010). *Quantum Computation and Quantum Information*. Cambridge.
2. [Montanaro2016] Montanaro, A. (2016). "Quantum Algorithms: An Overview." *npj Quantum Information*, 2, 15023.
3. [Shor1994] Shor, P. W. (1994). "Algorithms for Quantum Computation." *FOCS*, 124–134.
4. [Grover1996] Grover, L. K. (1996). "A Fast Quantum Mechanical Algorithm for Database Search." *STOC*, 212–219.
5. [Harrow2009] Harrow, A. W., Hassidim, A., & Lloyd, S. (2009). "Quantum Algorithm for Linear Systems of Equations." *PRL*, 103(15), 150502.
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
