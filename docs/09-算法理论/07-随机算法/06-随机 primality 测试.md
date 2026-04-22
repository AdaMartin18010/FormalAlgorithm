# 随机素性测试：Miller-Rabin

## 概述

Miller-Rabin 素性测试是密码学中最常用的随机算法之一。它以极小的错误概率判定一个数是否为素数，且远快于确定性算法（如 AKS，$O(n^{6+\varepsilon})$）。

## 理论基础

### Fermat 小定理

若 $p$ 为素数，$a$ 与 $p$ 互质：

$$a^{p-1} \equiv 1 \pmod{p}$$

**逆否命题**：若存在 $a$ 使 $a^{n-1} \not\equiv 1 \pmod{n}$，则 $n$ 为合数。

### 问题：Carmichael 数

某些合数对所有与 $n$ 互质的 $a$ 满足 Fermat 条件，如 561、1105、1729。

### 二次探测定理

若 $p$ 为素数且 $x^2 \equiv 1 \pmod{p}$，则 $x \equiv 1$ 或 $x \equiv -1 \pmod{p}$。

## Miller-Rabin 算法

### 步骤

1. 将 $n-1$ 写成 $2^s \cdot d$（$d$ 为奇数）
2. 随机选择基数 $a \in [2, n-2]$
3. 计算 $x = a^d \pmod{n}$
4. 若 $x = 1$ 或 $x = n-1$，通过测试
5. 重复 $s-1$ 次：$x = x^2 \pmod{n}$
   - 若 $x = n-1$，通过测试
   - 若 $x = 1$，失败（合数）
6. 若从未得到 $n-1$，失败（合数）

### 错误概率

- 单次测试：合数通过概率 $\leq 1/4$
- $k$ 次独立测试：错误概率 $\leq (1/4)^k$
- $k=10$：错误概率 $< 10^{-6}$
- $k=40$：错误概率 $< 10^{-24}$（低于硬件故障率）

## 确定性版本

对 64 位整数，测试特定的一组基数即可确定性判定：

$$a \in \{2, 325, 9375, 28178, 450775, 9780504, 1795265022\}$$

（Jim Sinclair, 2011）

## 代码参考

- TypeScript: `examples/algorithms-ts/src/number_theory.ts` → `isPrime()`
- Java: `examples/algorithms-java/NumberTheory.java` → `isPrime()`
- Go: `examples/algorithms-go/number_theory.go` → `IsPrime()`
- C++: `examples/algorithms-cpp/number_theory.cpp` → `isPrime()`
- Rust: `examples/algorithms/src/primality_test.rs`

## 应用

| 场景 | 用途 |
|------|------|
| RSA 密钥生成 | 生成大素数 $p, q$ |
| Diffie-Hellman | 选择安全素数模数 |
| 椭圆曲线 | 选择素数域 |
| 哈希表 | 选择素数大小的桶数 |
