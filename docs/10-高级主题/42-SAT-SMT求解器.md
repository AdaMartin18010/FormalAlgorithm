---
title: 42 SAT SMT求解器
concepts: ["量子算法", "机器学习", "并行计算", "流算法", "分布式算法"]
level: 中级
last_updated: 2026-04-21
---

# SAT/SMT 求解器原理


> **版本**: 1.0
> **创建日期**: 2026-04-19
> **最后更新**: 2026-04-19

> 对应课程：CMU 15-414 / Stanford CS 238V

## 1. SAT 求解

**可满足性问题（SAT）**：给定一个命题逻辑公式 $\varphi$（通常表示为合取范式 CNF），判定是否存在一个真值赋值使其为真。SAT 是第一个被证明的 NP-完全问题（Cook-Levin 定理）。

### 1.1 DPLL 算法

DPLL 算法由 Davis、Logemann 和 Loveland 在 1962 年提出，是当代 SAT 求解器的理论基础。

**核心规则**：

1. **单元传播（Unit Propagation）**：若子句中仅有一个文字未定，则该文字必须被赋值为真。形式化地，若子句 $C = (l \lor D)$ 且 $D$ 中所有文字已被赋假，则 $l$ 必须赋真。

2. **纯文字消除（Pure Literal Elimination）**：若变量 $v$ 仅以正文字或仅以负文字出现在剩余公式中，则可将 $v$ 赋值为相应极性并简化公式。

3. **回溯（Backtracking）**：当遇到冲突（空子句）时，撤销最近的决策赋值并尝试另一极性。

**DPLL 伪代码**：

```
function DPLL(φ, assignment):
    φ = UnitPropagate(φ, assignment)
    if φ contains empty clause: return UNSAT
    if φ has no clauses: return SAT(assignment)

    l = ChooseDecisionLiteral(φ)

    result = DPLL(φ ∧ l, assignment ∪ {l})
    if result == SAT: return result

    return DPLL(φ ∧ ¬l, assignment ∪ {¬l})
```

### 1.2 CDCL（Conflict-Driven Clause Learning）

现代 SAT 求解器采用 CDCL 框架，由 Marques-Silva 和 Sakallah 于 1999 年系统提出。CDCL 在 DPLL 基础上增加了**冲突分析**、**学习子句**和**非 Chronological 回溯**。

#### 蕴含图（Implication Graph）

蕴含图 $G = (V, E)$ 记录了单元传播产生的推导关系：

- 顶点：赋值文字 $l$（标注决策层级 $dl(l)$）
- 边：$(l_i, l)$ 当且仅当 $l$ 由单元传播从子句 $C$ 推出，且 $l_i \in C$

#### 冲突分析

当产生冲突子句 $C_\kappa$ 时，通过**反向边遍历**蕴含图找到**唯一蕴含点（UIP, Unique Implication Point）**。UIP 是从冲突节点到当前决策层级根节点的所有路径上的公共节点。

**第一 UIP（1-UIP）** 策略：选择离冲突节点最近的 UIP，生成学习子句：

$$C_{learn} = \text{resolve}(C_\kappa, \text{reason}(\kappa))$$

通过反复解析，直到子句中仅含一个当前层级的文字。

#### 决策启发式：VSIDS

**Variable State Independent Decaying Sum（VSIDS）**：为每个文字维护一个活动分数，冲突时增加相关文字分数，并定期衰减：

$$\text{score}(l) \leftarrow \text{score}(l) + \text{inc}$$
$$\text{inc} \leftarrow \text{inc} \times \text{decay}\quad (\text{decay} < 1)$$

决策时选择分数最高的未赋值变量。

#### 2-SAT 和 Horn-SAT

- **2-SAT**：每个子句最多含 2 个文字。可通过强连通分量（SCC）在 $O(n)$ 时间内求解：构造蕴含图 $G_\varphi$，$\varphi$ 可满足当且仅当不存在变量 $x$ 使得 $x$ 与 $\neg x$ 在同一 SCC 中。

- **Horn-SAT**：每个子句至多含一个正文字。可通过单元传播在 $O(n)$ 时间内求解：反复应用单元传播，若未产生冲突则可满足。

## 2. SMT 求解

**SMT（Satisfiability Modulo Theories）**：判定一阶逻辑公式在特定背景理论下的可满足性。

### 2.1 Nelson-Oppen 组合方法

Nelson-Oppen 方法组合多个签名不相交（signature-disjoint）的凸理论决策过程。

**条件**：

1. **签名不相交**：理论 $T_1, T_2$ 除等号外无共享函数/谓词符号
2. **凸性（Convexity）**：理论 $T$ 是凸的，若对任意合取公式 $\varphi$ 和变量等式集合 $E = \{x_i = y_i\}$，$\varphi \models_T \bigvee E$ 蕴含存在某个 $e \in E$ 使得 $\varphi \models_T e$

**等式传播（Equality Propagation）**：

- 将公式划分为纯子公式 $\varphi_1, \varphi_2$ 分别送往 $T_1, T_2$ 的求解器
- 若某理论推断出共享变量间的等式 $x = y$，则传播给另一理论
- 若某理论发现不可满足，则整体不可满足
- 若非凸理论，需进行**情形分裂（Case Split）**

### 2.2 DPLL(T) 框架

**延迟理论求解（Lazy Approach）**：

1. **抽象**：将原子公式 $a_i$ 映射为命题变量 $p_i$，得到布尔骨架 $\varphi_{bool}$
2. **SAT 求解**：调用 SAT 求解器生成候选模型 $M$
3. **理论求解**：将 $M$ 对应的原子集合 $T_M$ 送往理论求解器 $T$-Solver 检查一致性
4. **学习**：若不一致，从 $T_M$ 中提取**最小不可满足核（Minimal Unsatisfiable Core）** $C$，生成阻塞子句 $\bigvee_{a_i \in C} \neg p_i$ 加入 SAT 求解器

### 2.3 常见理论

| 理论 | 符号 | 可判定性 | 复杂度 | 说明 |
|------|------|----------|--------|------|
| 线性实数算术 | LRA | 可判定 | PTIME | Fourier-Motzkin 消元、Simplex |
| 线性整数算术 | LIA | 可判定 | NP-完全 | 整数规划、Cooper 算法 |
| 未解释函数 | EUF | 可判定 | PTIME | Congruence Closure |
| 数组理论 | AX | 可判定 | NP-完全 | read-over-write 公理 |
| 位向量 | BV | 可判定 | NP-完全 | 比特级/字级编码 |

**EUF 的 Congruence Closure**：

- 初始将所有项划分为单元素等价类
- 合并由等式约束产生的等价类
- 应用一致性规则：若 $s \sim t$ 则 $f(s) \sim f(t)$

## 3. 实现技术

### 3.1 重启策略（Restart）

定期进行搜索重启，保留学习子句但重置变量赋值。常用策略：

- **Geometric Restart**：重启间隔按几何级数增长 $r \times \alpha^k$
- **Luby Restart**：使用 Luby 序列 $1, 1, 2, 1, 1, 2, 4, 1, \dots$

### 3.2 子句删除

学习子句数量呈指数增长，需定期清理低质量子句：

- **LBD（Literal Block Distance）**：子句中不同决策层级的数量。LBD 小的子句更优质，优先保留
- **活动度（Activity）**：基于 VSIDS 风格的子句活动分数

### 3.3 Watched Literals

用于 $O(1)$ 复杂度的单元传播检测：

- 每个子句仅监视两个文字
- 当某监视文字被赋假时，扫描子句寻找新的未假文字作为新监视
- 若找不到，则触发单元传播；若另一监视文字也已假，则发生冲突

## 4. MiniSat / Z3 使用示例

### MiniSat（C++）

```cpp
#include "minisat/core/Solver.h"
using namespace Minisat;

Solver s;
Var a = s.newVar();
Var b = s.newVar();

// (a ∨ b) ∧ (¬a ∨ b)
s.addClause(mkLit(a), mkLit(b));
s.addClause(~mkLit(a), mkLit(b));

bool sat = s.solve();
if (sat) {
    std::cout << "SAT: a=" << toInt(s.modelValue(a))
              << ", b=" << toInt(s.modelValue(b)) << std::endl;
}
```

### Z3（Python）

```python
from z3 import *

x, y = Ints('x y')
s = Solver()

s.add(x > 2)
s.add(y < 10)
s.add(x + 2*y == 7)

if s.check() == sat:
    m = s.model()
    print(f"x = {m[x]}, y = {m[y]}")
else:
    print("UNSAT")
```

## 5. 参考文献

1. **Davis & Putnam (1960)**. *A Computing Procedure for Quantification Theory*. Journal of the ACM, 7(3):201-215. 奠定了早期 SAT 求解的理论基础。

2. **Marques-Silva, J. P. & Sakallah, K. A. (1999)**. *GRASP — A New Search Algorithm for Satisfiability*. ICCAD 1999. 系统提出了 CDCL 框架。

3. **Nelson, G. & Oppen, D. C. (1979)**. *Simplification by Cooperating Decision Procedures*. ACM Transactions on Programming Languages and Systems, 1(2):245-257. 提出了理论组合的经典方法。

4. **Moura, L. de & Bjørner, N. (2008)**. *Z3: An Efficient SMT Solver*. TACAS 2008. 描述了工业级 SMT 求解器 Z3 的设计与实现。

5. **Biere, A., Heule, M., van Maaren, H., & Walsh, T. (eds.) (2009)**. *Handbook of Satisfiability*. IOS Press. SAT 与 SMT 求解的权威参考书。

---

## 参考文献

- [BarrettTinelli2018]

---

## 知识导航

- [返回目录](README.md)

## 学习目标

- 理解SAT/SMT 求解器原理的核心概念
- 掌握SAT/SMT 求解器原理的形式化表示
