# 后缀数组与最长公共前缀（LCP）

## 概述

后缀数组（Suffix Array, SA）是字符串所有后缀按字典序排序后的起始位置数组。结合最长公共前缀数组（LCP），它可以高效解决大量字符串问题，且实现比后缀树更简洁。

## 后缀数组定义

对于字符串 $S$（长度为 $n$，通常末尾附加哨兵字符 `$`）：

$$SA[i] = \text{第 } i \text{ 小后缀的起始位置}$$

即 $S[SA[0]..] < S[SA[1]..] < ... < S[SA[n-1]..]$（字典序）。

## 构建算法

### 倍增法（$O(n \log n)$）

1. 初始：按单个字符排序，得到长度为 1 的等价类
2. 迭代：每次将比较长度翻倍，利用前一轮的排名进行排序
3. 使用计数排序（基数排序），每轮 $O(n)$
4. 共 $O(\log n)$ 轮，总时间 $O(n \log n)$

### SA-IS 算法（$O(n)$）

诱导排序（Induced Sorting）的线性时间算法，分为：

- **L-type**：后缀 $S[i..]$ 大于 $S[i+1..]$
- **S-type**：后缀 $S[i..]$ 小于 $S[i+1..]$
- **LMS**：Left-Most S-type，关键位置

通过递归诱导排序 LMS 子串，实现线性时间。

## LCP 数组（Kasai 算法）

$lcp[i]$ 表示后缀 $SA[i]$ 与 $SA[i-1]$ 的最长公共前缀长度。

### 线性时间构建

利用**排名数组** $rank[SA[i]] = i$ 和**高度递减**性质：

```
h = 0
for i = 0 to n-1:
    if rank[i] > 0:
        j = SA[rank[i] - 1]
        while S[i+h] == S[j+h]: h++
        lcp[rank[i]] = h
        if h > 0: h--
```

## 经典应用

| 问题 | 解法 |
|------|------|
| 不同子串个数 | $\sum_{i=1}^{n-1} (n - SA[i]) - lcp[i]$ |
| 最长重复子串 | $\max(lcp)$ |
| 最长公共子串（两串）| 拼接后求 $lcp$，排除跨边界 |
| 第 $k$ 小子串 | 按 SA 顺序，利用 lcp 去重计数 |
| 可重叠最长重复 $k$ 次 | 在 lcp 数组上找长度 $\geq k-1$ 的连续段最小值 |

## 后缀数组 vs 后缀树

| 特性 | 后缀数组 | 后缀树 |
|------|---------|--------|
| 空间 | $O(n)$ | $O(n)$（常数大）|
| 构建 | $O(n \log n)$ 或 $O(n)$ | $O(n)$ |
| 子串查询 | $O(|P| \log n)$（二分）| $O(|P|)$ |
| 实现难度 | 中等 | 高 |
| LCP 查询 | RMQ（$O(1)$ 预处理后）| 天然支持 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/string.ts` → `suffixArray()` / `lcpArray()`
- Rust: `examples/algorithms/src/suffix_array.rs`
- Go: `examples/algorithms-go/string.go`（可扩展）
