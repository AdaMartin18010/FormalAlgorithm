---
title: 字符串匹配与KMP应用 / String Matching and KMP Applications
version: 1.0
status: maintained
last_updated: 2026-04-23
owner: LeetCode面试专题工作组
concepts: ["前缀函数", "KMP自动机", "字符串匹配", " border", "回文串", "模式匹配"]
level: 中级到高级
leetcode_tags: ["string", "two-pointers", "string-matching"]
---

> 📊 **项目全面梳理**：详细的项目结构、模块详解和学习路径，请参阅 [`项目全面梳理-2025.md`](../../项目全面梳理-2025.md)

## 字符串匹配与KMP应用 / String Matching and KMP Applications

### 摘要 / Executive Summary

- 字符串匹配是计算机科学中最经典的问题之一，其应用涵盖文本编辑、生物信息学、网络入侵检测等领域。朴素匹配算法的 $O(nm)$ 时间复杂度在模式串较长时效率低下，而 Knuth-Morris-Pratt（KMP）算法通过**前缀函数**在 $O(n+m)$ 时间内完成匹配，是面试中区分候选人算法功底的重要考点。
- 本文从形式化定义出发，严格推导前缀函数的计算过程与 KMP 自动机的构造原理，通过 LeetCode 28（实现 strStr）和 214（最短回文串）两道经典题目展示 KMP 的实战应用。
- 核心学习目标：理解"**匹配失败时不回退文本指针**"的直觉，以及前缀函数如何编码这一信息。

### 关键术语与符号 / Glossary

| 术语 / Term | 定义 / Definition |
|-------------|-------------------|
| 前缀 Prefix | 字符串 $s$ 的前缀是 $s[0..i]$（$0 \leq i < |s|$），真前缀要求 $i < |s|-1$ |
| 后缀 Suffix | 字符串 $s$ 的后缀是 $s[i..|s|-1]$（$0 \leq i < |s|$），真后缀要求 $i > 0$ |
| Border | 同时是字符串真前缀和真后缀的子串 |
| 前缀函数 Prefix Function | $\pi[i] = $ $s[0..i]$ 的最长真 border 的长度 |
| KMP 自动机 KMP Automaton | 基于前缀函数构造的确定性有限自动机，用于模式匹配 |
| 失配函数 Failure Function | 自动机中状态转移的定义，决定匹配失败时的回退位置 |

术语对齐与引用规范：`docs/术语与符号总表.md`，`01-基础理论/00-撰写规范与引用指南.md`

### 目录 / Table of Contents

- [字符串匹配与KMP应用 / String Matching and KMP Applications](#字符串匹配与kmp应用--string-matching-and-kmp-applications)
  - [摘要 / Executive Summary](#摘要--executive-summary)
  - [关键术语与符号 / Glossary](#关键术语与符号--glossary)
  - [目录 / Table of Contents](#目录--table-of-contents)
  - [交叉引用与依赖 / Cross-References and Dependencies](#交叉引用与依赖--cross-references-and-dependencies)
- [1. 形式化定义 / Formal Definitions](#1-形式化定义--formal-definitions)
  - [1.1 字符串匹配问题实例](#11-字符串匹配问题实例)
  - [1.2 前缀函数的形式化定义](#12-前缀函数的形式化定义)
  - [1.3 KMP 自动机的形式化定义](#13-kmp-自动机的形式化定义)
- [2. 核心思路与算法框架](#2-核心思路与算法框架)
  - [2.1 前缀函数的递推计算](#21-前缀函数的递推计算)
  - [2.2 KMP 匹配过程](#22-kmp-匹配过程)
  - [2.3 KMP 在字符串构造问题中的应用](#23-kmp-在字符串构造问题中的应用)
- [3. 经典题目详解](#3-经典题目详解)
  - [3.1 LeetCode 28 — Implement strStr()](#31-leetcode-28--implement-strstr)
    - [形式化规约 / Formal Specification](#形式化规约--formal-specification)
    - [核心思路 / Core Idea](#核心思路--core-idea)
    - [代码实现 / Code Implementations](#代码实现--code-implementations)
    - [复杂度分析 / Complexity Analysis](#复杂度分析--complexity-analysis)
  - [3.2 LeetCode 214 — Shortest Palindrome](#32-leetcode-214--shortest-palindrome)
    - [形式化规约 / Formal Specification](#形式化规约--formal-specification-1)
    - [核心思路 / Core Idea](#核心思路--core-idea-1)
    - [代码实现 / Code Implementations](#代码实现--code-implementations-1)
    - [复杂度分析 / Complexity Analysis](#复杂度分析--complexity-analysis-1)
    - [正确性证明 / Correctness Proof](#正确性证明--correctness-proof)
- [4. 复杂度分析体系](#4-复杂度分析体系)
  - [4.1 字符串匹配算法对比](#41-字符串匹配算法对比)
  - [4.2 前缀函数计算复杂度分析](#42-前缀函数计算复杂度分析)
- [5. 正确性证明框架](#5-正确性证明框架)
  - [5.1 KMP 匹配正确性](#51-kmp-匹配正确性)
- [6. 思维表征](#6-思维表征)
  - [6.1 KMP 自动机状态转移图](#61-kmp-自动机状态转移图)
  - [6.2 前缀函数计算过程图](#62-前缀函数计算过程图)
  - [6.3 字符串匹配算法对比图](#63-字符串匹配算法对比图)
  - [6.4 公理定理证明树](#64-公理定理证明树)
- [7. 常见错误与反模式](#7-常见错误与反模式)
  - [7.1 前缀函数下标越界](#71-前缀函数下标越界)
  - [7.2 KMP 匹配后未继续](#72-kmp-匹配后未继续)
  - [7.3 混淆 border 与公共前后缀](#73-混淆-border-与公共前后缀)
- [8. 自测问题](#8-自测问题)
  - [问题 1：前缀函数与 Z 函数的关系](#问题-1前缀函数与-z-函数的关系)
  - [问题 2：为什么 KMP 中文本指针不回退？](#问题-2为什么-kmp-中文本指针不回退)
  - [问题 3：多个模式串匹配](#问题-3多个模式串匹配)
- [9. 学习目标](#9-学习目标)
- [参考文献 / References](#参考文献--references)

### 交叉引用与依赖 / Cross-References and Dependencies

**上游理论依赖 / Upstream Dependencies**:

- [`09-算法理论/01-算法基础/02-数据结构理论.md`](../../09-算法理论/01-算法基础/02-数据结构理论.md) — 字符串的数组表示
- [`04-算法复杂度/01-时间复杂度.md`](../../04-算法复杂度/01-时间复杂度.md) — 时间复杂度分析框架

**下游应用 / Downstream Applications**:

- `13-LeetCode算法面试专题/04-字符串专题/02-回文问题.md` — KMP 在回文问题中的应用

---

## 1. 形式化定义 / Formal Definitions

### 1.1 字符串匹配问题实例

**定义 1.1** (字符串匹配问题 / String Matching Problem)
给定文本串 $T$（长度为 $n$）和模式串 $P$（长度为 $m$），找出 $T$ 中所有 $P$ 出现的起始位置。

形式化地，求集合：

$$
\{ i \in [0, n-m] \mid T[i..i+m-1] = P[0..m-1] \}
$$

**定义 1.2** (朴素匹配算法 / Naive Matching)
对于每个起始位置 $i \in [0, n-m]$，逐个比较 $T[i+j]$ 与 $P[j]$（$j = 0, 1, \ldots, m-1$）。若全部相等，则 $i$ 是一个匹配位置。

朴素算法的最坏时间复杂度为 $O(nm)$，发生在 $T = \text{\"aaaa...a\"}$ 且 $P = \text{\"aaa...ab\"}$ 的情况。

### 1.2 前缀函数的形式化定义

**定义 1.3** (Border)
字符串 $s$ 的 border 是同时是 $s$ 的**真前缀**和**真后缀**的非空子串。

**定义 1.4** (前缀函数 / Prefix Function) [Knuth-Morris-Pratt 1977]
对于字符串 $s$，其前缀函数 $\pi$ 定义为：

$$
\pi[i] = \max_{0 \leq k \leq i} \{ k \mid s[0..k-1] = s[i-k+1..i] \}
$$

即 $\pi[i]$ 是子串 $s[0..i]$ 的最长真 border 的长度。若不存在 border，则 $\pi[i] = 0$。

**示例**: 对于 $s = \text{\"abcabcd\"}$

| $i$ | $s[i]$ | $s[0..i]$ | 最长真 border | $\pi[i]$ |
|-----|--------|-----------|--------------|---------|
| 0 | a | a | 无 | 0 |
| 1 | b | ab | 无 | 0 |
| 2 | c | abc | 无 | 0 |
| 3 | a | abca | a | 1 |
| 4 | b | abcab | ab | 2 |
| 5 | c | abcabc | abc | 3 |
| 6 | d | abcabcd | 无 | 0 |

### 1.3 KMP 自动机的形式化定义

**定义 1.5** (KMP 自动机 / KMP Automaton)
KMP 自动机是一个确定性有限自动机（DFA），状态集为 $\{0, 1, \ldots, m\}$，其中状态 $k$ 表示"当前已匹配模式串的前 $k$ 个字符"。

状态转移函数 $\delta(k, c)$ 定义为：

$$
\delta(k, c) = \begin{cases}
k + 1, & \text{if } P[k] = c \\
\delta(\pi[k-1], c), & \text{if } k > 0 \text{ and } P[k] \neq c \\
0, & \text{if } k = 0 \text{ and } P[0] \neq c
\end{cases}
$$

---

## 2. 核心思路与算法框架

### 2.1 前缀函数的递推计算

前缀函数可以在 $O(m)$ 时间内递推计算：

```text
ComputePrefixFunction(P):
    m ← |P|
    π[0] ← 0
    k ← 0
    for q ← 1 to m-1:
        while k > 0 and P[k] ≠ P[q]:
            k ← π[k-1]
        if P[k] = P[q]:
            k ← k + 1
        π[q] ← k
    return π
```

**核心直觉**: 计算 $\pi[q]$ 时，利用已知的 $\pi[0..q-1]$ 信息。若当前字符匹配，则 border 长度加 1；若不匹配，则回退到次长的候选 border。

### 2.2 KMP 匹配过程

```text
KMP-Matcher(T, P):
    n ← |T|, m ← |P|
    π ← ComputePrefixFunction(P)
    q ← 0  // 当前匹配长度
    for i ← 0 to n-1:
        while q > 0 and P[q] ≠ T[i]:
            q ← π[q-1]
        if P[q] = T[i]:
            q ← q + 1
        if q = m:
            输出匹配位置 i - m + 1
            q ← π[q-1]  // 继续寻找下一个匹配
```

**核心直觉**: 文本指针 $i$ **永不回退**。当失配时，利用前缀函数将模式串向右滑动到最大安全位置。

### 2.3 KMP 在字符串构造问题中的应用

KMP 不仅可以用于查找，还可以用于分析字符串自身的结构：

- **最短重复子串**: 若 $n - \pi[n-1]$ 整除 $n$，则最短重复子串长度为 $n - \pi[n-1]$
- **字符串拼接构造**: 如最短回文串问题，利用前缀函数找最长前缀回文

---

## 3. 经典题目详解

### 3.1 LeetCode 28 — Implement strStr()

> **题目链接 / Problem Link**: [LeetCode 28. Implement strStr()](https://leetcode.com/problems/implement-strstr/)
> **难度 / Difficulty**: Easy

#### 形式化规约 / Formal Specification

**输入 / Input**: 文本串 $haystack$（长度 $n$）和模式串 $needle$（长度 $m$）。
**输出 / Output**: $needle$ 在 $haystack$ 中第一次出现的起始索引，若不存在则返回 $-1$。
**前置条件 / Precondition**: $n, m \geq 0$。
**后置条件 / Postcondition**:

$$
\text{result} = \begin{cases}
\min \{ i \mid haystack[i..i+m-1] = needle \}, & \text{if exists} \\
-1, & \text{otherwise}
\end{cases}
$$

#### 核心思路 / Core Idea

**方法：KMP 算法**

先计算 `needle` 的前缀函数，然后用 KMP 匹配过程在 `haystack` 中搜索。

#### 代码实现 / Code Implementations

- **Python**: [`examples/algorithms-python/src/leetcode/lc0028_implement_strstr.py`](../../../examples/algorithms-python/src/leetcode/lc0028_implement_strstr.py)
- **Rust**: [`examples/algorithms/src/leetcode/lc0028_implement_strstr.rs`](../../../examples/algorithms/src/leetcode/lc0028_implement_strstr.rs)

```python
# Python KMP 实现
def str_str(haystack: str, needle: str) -> int:
    if not needle:
        return 0

    # 计算前缀函数
    def compute_prefix(p: str) -> list[int]:
        m = len(p)
        pi = [0] * m
        k = 0
        for q in range(1, m):
            while k > 0 and p[k] != p[q]:
                k = pi[k - 1]
            if p[k] == p[q]:
                k += 1
            pi[q] = k
        return pi

    pi = compute_prefix(needle)
    q = 0
    for i in range(len(haystack)):
        while q > 0 and needle[q] != haystack[i]:
            q = pi[q - 1]
        if needle[q] == haystack[i]:
            q += 1
        if q == len(needle):
            return i - len(needle) + 1

    return -1
```

```rust
// Rust KMP 实现
pub fn str_str(haystack: String, needle: String) -> i32 {
    if needle.is_empty() {
        return 0;
    }
    let n = haystack.len();
    let m = needle.len();
    let h: Vec<char> = haystack.chars().collect();
    let p: Vec<char> = needle.chars().collect();

    // 计算前缀函数
    let mut pi = vec![0; m];
    let mut k = 0;
    for q in 1..m {
        while k > 0 && p[k] != p[q] {
            k = pi[k - 1];
        }
        if p[k] == p[q] {
            k += 1;
        }
        pi[q] = k;
    }

    // KMP 匹配
    let mut q = 0;
    for i in 0..n {
        while q > 0 && p[q] != h[i] {
            q = pi[q - 1];
        }
        if p[q] == h[i] {
            q += 1;
        }
        if q == m {
            return (i - m + 1) as i32;
        }
    }
    -1
}
```

#### 复杂度分析 / Complexity Analysis

| 指标 / Metric | 值 / Value | 说明 / Note |
|--------------|-----------|------------|
| 时间复杂度 / Time | $O(n + m)$ | 前缀函数 $O(m)$ + 匹配 $O(n)$ |
| 空间复杂度 / Space | $O(m)$ | 前缀函数数组 |

---

### 3.2 LeetCode 214 — Shortest Palindrome

> **题目链接 / Problem Link**: [LeetCode 214. Shortest Palindrome](https://leetcode.com/problems/shortest-palindrome/)
> **难度 / Difficulty**: Hard

#### 形式化规约 / Formal Specification

**输入 / Input**: 字符串 $s$（长度 $n$）。
**输出 / Output**: 通过在 $s$ 前面添加字符，使其成为最短的回文串。
**前置条件 / Precondition**: $s$ 由小写英文字母组成，$n \geq 0$。
**后置条件 / Postcondition**: 返回字符串 $result = t + s$，其中 $t$ 是最短的前缀串，使得 $result$ 是回文串。

#### 核心思路 / Core Idea

**关键观察**: 若 $s$ 的最长前缀回文子串长度为 $L$，则只需将 $s[L..n-1]$ 的逆序添加到 $s$ 前面即可。

**如何求最长前缀回文？**

构造新字符串 $combined = s + \text{\"#\"} + s.reverse()$，然后计算 $combined$ 的前缀函数。$combined$ 末尾的前缀函数值即为 $s$ 的最长前缀回文长度。

**原理**: $combined$ 末尾的前缀函数值表示 $s.reverse()$ 的某个后缀与 $s$ 的某个前缀的最大匹配长度。由于中间有分隔符 `#`，这个匹配必然完全落在 $s$ 和 $s.reverse()$ 内部，即对应 $s$ 的一个前缀回文。

#### 代码实现 / Code Implementations

- **Python**: [`examples/algorithms-python/src/leetcode/lc0214_shortest_palindrome.py`](../../../examples/algorithms-python/src/leetcode/lc0214_shortest_palindrome.py)

```python
# Python KMP 实现
def shortest_palindrome(s: str) -> str:
    if not s:
        return s

    rev = s[::-1]
    combined = s + "#" + rev

    # 计算前缀函数
    n = len(combined)
    pi = [0] * n
    k = 0
    for q in range(1, n):
        while k > 0 and combined[k] != combined[q]:
            k = pi[k - 1]
        if combined[k] == combined[q]:
            k += 1
        pi[q] = k

    # 最长前缀回文长度 = pi[-1]
    longest_prefix_palindrome = pi[-1]
    to_add = s[longest_prefix_palindrome:][::-1]
    return to_add + s
```

#### 复杂度分析 / Complexity Analysis

| 指标 / Metric | 值 / Value | 说明 / Note |
|--------------|-----------|------------|
| 时间复杂度 / Time | $O(n)$ | 前缀函数计算，$combined$ 长度为 $2n+1$ |
| 空间复杂度 / Space | $O(n)$ | 前缀函数数组和拼接字符串 |

#### 正确性证明 / Correctness Proof

**定理 3.2.1** (最短回文串构造正确性): 算法返回的字符串是通过在 $s$ 前添加最少字符形成的回文串。

**证明 / Proof**:

**引理 3.2.1**: 设 $L$ 为 $s$ 的最长前缀回文子串长度。则最短回文串构造为 $s[L..n-1]^{R} + s$。

**引理证明**: 任何通过在前端添加字符使 $s$ 成为回文串的方案，必须保证添加后串的前半部分与后半部分对称。设添加了 $t$ 个字符，则回文串长度为 $n + |t|$。为使整个串回文，原串 $s$ 的某个前缀必须自身是回文（作为中心对称轴），且剩余部分 $s[L..n-1]$ 的对称补被添加到前端。为使 $|t|$ 最小，需要 $L$ 最大。$\square$

**引理 3.2.2**: 对 $combined = s + \text{\"#\"} + s^R$，有 $\pi[|combined|-1] = L$。

**引理证明**: $\pi$ 的末位值表示 $combined$ 的最长真 border 长度。由于 `#` 不在 $s$ 中出现，任何 border 都不能跨越 `#`。因此 border 必然是 $s^R$ 的某个后缀与 $s$ 的某个前缀的匹配。设匹配长度为 $k$，则 $s[0..k-1] = s^R[n-k..n-1]$，即 $s[0..k-1] = s[k-1..0]^R$，这等价于 $s[0..k-1]$ 是回文。最大 $k$ 即为最长前缀回文长度 $L$。$\square$

**主定理证明**: 由引理 3.2.2，算法正确求得 $L$。由引理 3.2.1，$s[L..n-1]^R + s$ 是最短回文串。算法返回的正是此串，因此正确。$\square$

---

## 4. 复杂度分析体系

### 4.1 字符串匹配算法对比

| 算法 | 预处理时间 | 匹配时间 | 空间复杂度 | 备注 |
|-----|-----------|---------|-----------|------|
| 朴素算法 | $O(1)$ | $O(nm)$ | $O(1)$ | 简单但慢 |
| KMP | $O(m)$ | $O(n)$ | $O(m)$ | 线性最优 |
| Rabin-Karp | $O(m)$ | $O(n)$ 期望 | $O(1)$ | 哈希碰撞退化 |
| Boyer-Moore | $O(m + |\Sigma|)$ | $O(nm)$ 最坏 | $O(|\Sigma|)$ | 实际很快 |
| Z 算法 | $O(n)$ | $O(n)$ | $O(n)$ | 类似前缀函数 |

### 4.2 前缀函数计算复杂度分析

**定理 4.1** (前缀函数计算复杂度): `ComputePrefixFunction` 的时间复杂度为 $O(m)$。

**证明**:

外层循环执行 $m-1$ 次。内层 `while` 循环中，$k$ 的值只能减小（$k \leftarrow \pi[k-1]$），且每次进入外层循环的 `if` 分支时 $k$ 最多增加 1。由于 $k \geq 0$ 且 $k$ 的增加总量不超过 $m$，因此 `while` 循环的总执行次数也不超过 $m$。总时间为 $O(m)$。$\square$

---

## 5. 正确性证明框架

### 5.1 KMP 匹配正确性

**定理 5.1** (KMP 匹配正确性): KMP-Matcher 正确找出文本串 $T$ 中模式串 $P$ 的所有出现位置。

**证明 / Proof**:

**循环不变式**: 在第 $i$ 次迭代开始时（处理 $T[i]$ 之前），$q$ 的值满足：

$$
q = \max \{ k \mid P[0..k-1] = T[i-k..i-1] \}
$$

即 $q$ 是以 $T[i-1]$ 结尾的最长 $P$ 前缀匹配长度。

**初始化**: $i = 0$ 时，$q = 0$。空串与任何串的后缀匹配长度为 0，成立。

**保持**: 处理 $T[i]$ 时，分两种情况：

- **情况 A**: $P[q] = T[i]$。匹配长度增加 1，$q \leftarrow q + 1$。不变式对 $i+1$ 成立。
- **情况 B**: $P[q] \neq T[i]$。通过 $q \leftarrow \pi[q-1]$ 回退到次长匹配。由前缀函数定义，$P[0..\pi[q-1]-1]$ 是 $P[0..q-1]$ 的最长真 border，因此也是 $T[i-\pi[q-1]..i-1]$ 的后缀。回退后不变式恢复。重复直到 $q = 0$ 或匹配成功。

**终止**: 当 $q = m$ 时，$P[0..m-1] = T[i-m+1..i]$，找到一个匹配。输出后 $q \leftarrow \pi[m-1]$，继续寻找下一个可能重叠的匹配。

所有匹配位置均被找到且无遗漏。$\square$

---

## 6. 思维表征

### 6.1 KMP 自动机状态转移图

```mermaid
flowchart LR
    S0[状态0] -->|a| S1[状态1]
    S1 -->|b| S2[状态2]
    S2 -->|a| S3[状态3]
    S3 -->|b| S4[状态4<br/>匹配成功]
    S1 -->|a| S1
    S2 -->|b| S0
    S3 -->|b| S0
    S0 -->|b| S0

    S4 -->|回退 π[3]=2| S2
```

> 示例：模式串 "abab"

### 6.2 前缀函数计算过程图

```mermaid
flowchart TD
    Start[初始化 π[0]=0, k=0] --> Loop[遍历 q=1..m-1]
    Loop --> While{P[k] != P[q] && k > 0}
    While -->|是| UpdateK[k = π[k-1]]
    UpdateK --> While
    While -->|否| Check{P[k] == P[q]}
    Check -->|是| IncK[k += 1]
    Check -->|否| Skip[跳过]
    IncK --> SetPi[π[q] = k]
    Skip --> SetPi
    SetPi --> NextQ[q += 1]
    NextQ --> More{q < m?}
    More -->|是| Loop
    More -->|否| Done[返回 π]
```

### 6.3 字符串匹配算法对比图

```mermaid
flowchart TD
    Start[字符串匹配] --> Q1{模式串是否固定？}
    Q1 -->|是，多次查询| Q2{需要最坏情况线性？}
    Q1 -->|否，单次查询| A1[朴素算法 O(nm)]

    Q2 -->|是| A2[KMP O(n+m)]
    Q2 -->|否，期望快| A3[Rabin-Karp O(n)期望]
    Q2 -->|实际文本很长| A4[Boyer-Moore 通常很快]

    style A2 fill:#e1f5e1
```

### 6.4 公理定理证明树

```mermaid
flowchart BT
    A1[公理: 前缀函数递归定义] --> B1[引理: π[q] < q]
    A2[公理: Border 传递性] --> B2[引理: 次长 border = border 的 border]
    B1 --> C1[定理: 前缀函数计算 O(m)]
    B2 --> C1
    C1 --> D1[定理: KMP 匹配 O(n+m)]
    A3[公理: 文本指针单调性] --> D1
    D1 --> E1[推论: KMP 最优单模式匹配]
    D1 --> E2[应用: 最短回文串 O(n)]

    style C1 fill:#e1f5e1
    style D1 fill:#e1f5e1
    style E1 fill:#d4edda
    style E2 fill:#d4edda
```

---

## 7. 常见错误与反模式

### 7.1 前缀函数下标越界

**错误 / Mistake**: 在 `while k > 0 and p[k] != p[q]` 中，当 $k = 0$ 时访问 `pi[-1]`。

```python
# 错误
while k > 0 and p[k] != p[q]:
    k = pi[k - 1]  # 当 k 最终变为 0 时，循环条件不满足，不会执行此行
# 但如果写错条件：
while p[k] != p[q]:  # ❌ k=0 时若还不匹配，k = pi[-1] 越界
    k = pi[k - 1]

# 正确
while k > 0 and p[k] != p[q]:  # ✅ 先检查 k > 0
    k = pi[k - 1]
```

### 7.2 KMP 匹配后未继续

**错误 / Mistake**: 找到一个匹配后直接将 $q$ 置为 0，漏掉重叠匹配。

```python
# 错误
if q == m:
    result.append(i - m + 1)
    q = 0  # ❌ 可能漏掉重叠匹配，如 "aaaa" 中找 "aa"

# 正确
if q == m:
    result.append(i - m + 1)
    q = pi[q - 1]  # ✅ 回退到最大 border，继续寻找
```

### 7.3 混淆 border 与公共前后缀

**错误 / Mistake**: 认为 border 可以等于字符串本身。前缀函数中的 border 必须是**真**前缀和**真**后缀，因此 $\pi[i] \leq i$ 且不能等于 $i+1$。

---

## 8. 自测问题

### 问题 1：前缀函数与 Z 函数的关系

**Q**: 前缀函数（prefix function）和 Z 函数（Z-function）有何关系？

**A**: 两者都用于分析字符串的自相似性，但视角不同：

- **前缀函数** $\pi[i]$：以位置 $i$ 结尾的子串的最长 border 长度
- **Z 函数** $z[i]$：从位置 $i$ 开始的子串与整个字符串的最长公共前缀长度

两者可以互相转换。在实际应用中，Z 函数常用于多模式匹配（如后缀数组构建），前缀函数更常用于 KMP 和单模式匹配。

### 问题 2：为什么 KMP 中文本指针不回退？

**Q**: KMP 的核心优化是"文本指针不回退"，这一性质如何保证？

**A**: 当在文本位置 $i$ 、模式位置 $q$ 处失配时，前缀函数告诉我们：模式串可以向右滑动到位置 $\pi[q-1]$，而不需要回溯文本指针。这是因为 $P[0..\pi[q-1]-1]$ 已经匹配了 $T$ 的对应后缀（由 border 定义）。我们**已经知道**这部分匹配信息，不需要重新比较。

### 问题 3：多个模式串匹配

**Q**: 如果需要同时匹配多个模式串，KMP 如何扩展？

**A**: 可以构建**Aho-Corasick 自动机**，它是 KMP 自动机在多模式串上的推广。将多个模式串构建成 Trie 树，然后在每个节点上计算"失败指针"（类似 KMP 的 $\pi$），实现 $O(n + m + z)$ 的多模式匹配，其中 $z$ 是匹配输出总数。

---

## 9. 学习目标

完成本章学习后，读者应能够：

1. **形式化定义**前缀函数和 border，手动计算任意字符串的前缀函数。
2. **理解 KMP 自动机**的状态转移逻辑，解释为何文本指针不回退。
3. **独立实现** KMP 算法的前缀函数计算和匹配过程。
4. **应用 KMP 思想**解决字符串构造问题（如最短回文串、重复子串检测）。
5. **证明 KMP 的正确性**，包括前缀函数计算和匹配过程的两个核心定理。

---

## 参考文献 / References

- [Knuth-Morris-Pratt 1977]: Knuth, D. E., Morris, J. H., & Pratt, V. R. (1977). "Fast Pattern Matching in Strings." *SIAM Journal on Computing*, 6(2), 323-350.
- [Cormen 2022]: Cormen, T. H., et al. (2022). *Introduction to Algorithms* (4th ed.). MIT Press. §32.4 The Knuth-Morris-Pratt Algorithm.
- LeetCode 28 官方题解：<https://leetcode.com/problems/implement-strstr/solution/>
- LeetCode 214 官方题解：<https://leetcode.com/problems/shortest-palindrome/solution/>
