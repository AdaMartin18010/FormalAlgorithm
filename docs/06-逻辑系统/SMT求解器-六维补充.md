---
title: SMT求解器-六维补充
category: 06-逻辑系统
concepts: ["SMT", "SAT", "决策过程", "Egraph", "DPLL(T)"]
level: 高级
last_updated: 2026-04-21
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
- **UNSAT**: $T \models 
eg \phi$
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

**算法**: 使用 Union-Find 数据结构维护等价类，时间 $O(|T| lpha(|T|))$。

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
