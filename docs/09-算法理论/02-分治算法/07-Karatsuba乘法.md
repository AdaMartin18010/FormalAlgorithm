# Karatsuba 快速乘法

## 概述

Karatsuba 算法（1960）是第一个突破 $O(n^2)$ 的大整数乘法算法。对于 $n$ 位数字，它将复杂度降至 $O(n^{\log_2 3}) \approx O(n^{1.585})$，展示了分治策略在算术运算中的威力。

## 核心思想

将两个 $n$ 位数 $x$ 和 $y$ 各分为两半：

$$x = x_1 \cdot 10^{n/2} + x_0, \quad y = y_1 \cdot 10^{n/2} + y_0$$

传统方法需要 4 次乘法：

$$xy = x_1 y_1 \cdot 10^n + (x_1 y_0 + x_0 y_1) \cdot 10^{n/2} + x_0 y_0$$

Karatsuba 发现中间项可通过 3 次乘法得到：

$$z_2 = x_1 y_1$$
$$z_0 = x_0 y_0$$
$$z_1 = (x_1 + x_0)(y_1 + y_0) - z_2 - z_0$$

则 $xy = z_2 \cdot 10^n + z_1 \cdot 10^{n/2} + z_0$

## 复杂度分析

递归式：$T(n) = 3T(n/2) + O(n)$

由主定理：$T(n) = O(n^{\log_2 3}) \approx O(n^{1.585})$

## Toom-Cook 推广

Karatsuba 是 Toom-Cook 算法的特例（将数分为 $k$ 段）：

| 算法 | 分段 | 乘法次数 | 复杂度 |
|------|------|---------|--------|
| 传统 | 1 | 4 | $O(n^2)$ |
| Karatsuba | 2 | 3 | $O(n^{1.585})$ |
| Toom-3 | 3 | 5 | $O(n^{1.465})$ |
| Toom-4 | 4 | 7 | $O(n^{1.404})$ |

## FFT 乘法

对极大数（数千位以上），使用 FFT 实现 $O(n \log n)$ 乘法：

- 将数字视为多项式系数
- FFT 转换到频域相乘
- IFFT 得到结果

GMP、OpenSSL 等库在特定位数阈值切换算法：

- 小数字：传统 $O(n^2)$
- 中数字：Karatsuba / Toom-Cook
- 大数字：FFT（Schönhage-Strassen）

## 代码参考

- TypeScript: `examples/algorithms-ts/src/advanced.ts` → `multiplyPolynomials()`（FFT 版）
- Rust: `examples/algorithms/src/polynomial.rs`（可扩展）
