# Manacher 算法

## 概述

Manacher 算法（1975）用于在线性时间 $O(n)$ 内找出字符串的所有回文子串。它是字符串算法中最优雅的实现之一，通过巧妙利用回文的对称性避免重复计算。

## 问题定义

**回文串**：正读和反读相同的字符串，如 "aba"、"abba"。

**目标**：对字符串 $S$ 的每个位置 $i$，求以 $i$ 为中心的最长回文半径。

## 统一奇偶长度

通过在字符间插入分隔符（如 `#`），将所有回文统一为奇数长度：

```
"abba" → "^#a#b#b#a#$"
```

- `^` 和 `$` 为哨兵，避免边界检查
- 原字符串的每个字符和间隙都对应新串的一个位置

## 核心思想

维护当前最右回文的中心 $C$ 和右边界 $R$：

```
for i = 1 to n-2:
    mirror = 2*C - i
    if i < R:
        P[i] = min(R-i, P[mirror])
    while T[i+1+P[i]] == T[i-1-P[i]]:
        P[i]++
    if i + P[i] > R:
        C = i
        R = i + P[i]
```

### 对称点优化

若 $i$ 在当前最右回文内，其对称点 `mirror` 的回文信息可被利用：

- 若 `P[mirror]` 完全包含在 $[C-R, C+R]$ 内，则 `P[i] = P[mirror]`
- 否则至少知道 `P[i] >= R-i`，只需继续向外扩展

## 应用

| 问题 | Manacher 解法 |
|------|-------------|
| 最长回文子串 | `max(P[i])` 对应的子串 |
| 回文子串个数 | `sum((P[i]+1)/2)` |
| 以 $i$ 结尾的最长回文 | 扫描时记录 |
| 回文分割（最少段数）| DP + Manacher 预处理 |

## 与中心扩展的对比

| 方法 | 时间 | 空间 | 实现难度 |
|------|------|------|---------|
| 中心扩展 | $O(n^2)$ | $O(1)$ | 简单 |
| **Manacher** | **$O(n)$** | **$O(n)$** | **中等** |
| 后缀数组 + LCP | $O(n \log n)$ | $O(n)$ | 复杂 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/string.ts` → `manacher()`
- Java: `examples/algorithms-java/StringAlgorithms.java` → `manacher()`
- Go: `examples/algorithms-go/string.go` → `Manacher()`
- Rust: `examples/algorithms/src/manacher.rs`
