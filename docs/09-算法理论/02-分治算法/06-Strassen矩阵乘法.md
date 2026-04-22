# Strassen 矩阵乘法

## 概述

Strassen 算法（1969）是第一个突破 $O(n^3)$ 的矩阵乘法算法。对于 $n \times n$ 矩阵，它将复杂度从 $O(n^3)$ 降至 $O(n^{\log_2 7}) \approx O(n^{2.807})$，展示了分治策略在代数问题中的强大威力。

## 标准矩阵乘法的问题

对于 $2 \times 2$ 分块矩阵：

$$
\begin{pmatrix} A & B \\ C & D \end{pmatrix} \times \begin{pmatrix} E & F \\ G & H \end{pmatrix} = \begin{pmatrix} AE+BG & AF+BH \\ CE+DG & CF+DH \end{pmatrix}
$$

标准方法需要 8 次乘法 + 4 次加法。

## Strassen 的核心技巧

Strassen 发现只需 **7 次乘法**即可计算结果：

$$
\begin{aligned}
M_1 &= (A+D)(E+H) \\
M_2 &= (C+D)E \\
M_3 &= A(F-H) \\
M_4 &= D(G-E) \\
M_5 &= (A+B)H \\
M_6 &= (C-A)(E+F) \\
M_7 &= (B-D)(G+H)
\end{aligned}
$$

结果块：

$$
\begin{aligned}
P &= M_1 + M_4 - M_5 + M_7 \\
Q &= M_3 + M_5 \\
R &= M_2 + M_4 \\
S &= M_1 - M_2 + M_3 + M_6
\end{aligned}
$$

## 复杂度分析

递归式：$T(n) = 7T(n/2) + O(n^2)$

由主定理：$T(n) = O(n^{\log_2 7}) \approx O(n^{2.807})$

## 实际应用与局限

| 特性 | 说明 |
|------|------|
| 常数因子 | 较大，实际 $n < 100$ 时不如标准算法 |
| 数值稳定性 | 浮点运算中误差累积更严重 |
| 内存访问 | 非连续访问多，缓存效率低 |
| 实际交叉点 | 通常 $n > 1000$ 才开始优于标准算法 |

## 后续发展

| 年份 | 算法 | 指数 |
|------|------|------|
| 1969 | Strassen | 2.807 |
| 1978 | Pan | 2.796 |
| 1981 | Schönhage | 2.522 |
| 1987 | Coppersmith-Winograd | 2.376 |
| 2014 | Le Gall | 2.373 |
| 2023 | Duan-Wu-Zhou | 2.371 |

**理论下界**：矩阵乘法至少需要 $O(n^2)$ 时间（输出有 $n^2$ 个元素）。是否存在 $O(n^{2+\varepsilon})$ 的算法是开放问题。

## 代码参考

- TypeScript: `examples/algorithms-ts/src/`（可扩展）
- Rust: `examples/algorithms/src/matrix_operations.rs`（可扩展）
