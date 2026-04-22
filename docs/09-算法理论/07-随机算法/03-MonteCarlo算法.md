# Monte Carlo 算法

## 概述

Monte Carlo 算法是一类以**随机采样**为核心的随机算法。与 Las Vegas 算法（永远正确但运行时间随机）不同，Monte Carlo 算法在**固定时间内终止**，但结果可能以较小概率出错。

## 形式化定义

- **Yes-biased**：若答案为"是"，永远返回"是"；若答案为"否"，以概率 $\leq \varepsilon$ 错误返回"是"
- **No-biased**：对称定义
- **双侧错误**：两类错误概率均 $\leq \varepsilon$

通过独立重复运行 $k$ 次，可将错误概率降至 $\varepsilon^k$。

## 经典应用

### 1. 素性测试（Miller-Rabin）

- **双侧错误**：合数被误判为素数的概率 $\leq 1/4$ 每次
- 重复 $k$ 次，错误概率 $\leq (1/4)^k$
- 对 $k=10$，错误概率 $< 10^{-6}$

### 2. 矩阵乘法验证（Freivalds' Algorithm）

验证 $A \times B = C$：

- 随机向量 $r \in \{0,1\}^n$
- 检查 $A(Br) = Cr$
- 若 $AB \neq C$，错误通过的概率 $\leq 1/2$
- 时间 $O(n^2)$，远快于矩阵乘法 $O(n^\omega)$

### 3. 随机游走估计（PageRank）

通过模拟随机游走来估计网页重要性，而非精确求解大规模线性方程组。

### 4. 体积估计

高维凸体体积的确定性算法需要指数时间，而 Monte Carlo 随机采样可在多项式时间内给出 $(1+\varepsilon)$-近似。

## 与 Las Vegas 算法的对比

| 特性 | Monte Carlo | Las Vegas |
|------|------------|-----------|
| 运行时间 | 确定 | 随机（期望有界）|
| 结果正确性 | 概率保证 | 永远正确 |
| 可重复验证 | 通常不可 | 结果可验证 |
| 代表算法 | Miller-Rabin、Freivalds | 随机快速排序、随机选择 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/number_theory.ts` → `isPrime()`（Miller-Rabin）
- Java: `examples/algorithms-java/NumberTheory.java` → `isPrime()`
- Go: `examples/algorithms-go/number_theory.go` → `IsPrime()`
- Rust: `examples/algorithms/src/primality_test.rs`
