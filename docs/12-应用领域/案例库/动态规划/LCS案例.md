# 案例：LCS在版本控制差异比较与文档比对中的应用

## 背景

版本控制系统（Git、SVN）的核心功能之一是展示两个版本之间的差异（diff）。文档比对工具（如 Microsoft Word 的"比较文档"）需要找出两个文本的最长公共子序列（Longest Common Subsequence, LCS），从而精确标注新增、删除和修改的内容。

## 问题定义

- **输入**：两个文本序列 $A$（旧版本）和 $B$（新版本）
- **输出**：
  - LCS 长度和内容
  - 将 $A$ 转换为 $B$ 的最少编辑操作（插入、删除）

## LCS 与 Diff 的关系

Diff 算法的核心是求 LCS：

- 不属于 LCS 的 $A$ 中元素 = 删除内容
- 不属于 LCS 的 $B$ 中元素 = 新增内容

### Myers 差分算法

Git 使用的 diff 算法是 LCS 的优化版本：

- 将问题建模为编辑图上的最短路径
- 使用贪心 + 对角线移动优化
- 时间：$O(ND)$，$N$ 为总长度，$D$ 为编辑距离
- 对大部分相似文本，$D \ll N$，实际接近线性

## 动态规划解法

### 标准 LCS

$$dp[i][j] = \begin{cases} dp[i-1][j-1] + 1 & A[i] = B[j] \\ \max(dp[i-1][j], dp[i][j-1]) & \text{否则} \end{cases}$$

时间：$O(mn)$，空间：$O(mn)$（可优化至 $O(\min(m,n))$）

### 空间优化：Hirschberg 算法

- 将问题分治，每次只求中间列的 DP 值
- 时间保持 $O(mn)$，空间降至 $O(\min(m,n))$
- 适合处理大文件（如数MB的源代码）

## 实际系统

### Git Diff

```bash
git diff old_file new_file
```

- 行级 LCS：将文件按行分词
- 支持多种 diff 算法：`--minimal`、`--patience`、`--histogram`
- Patience diff：优先匹配不重复的行，对人类更友好

### 文档比对

- Word / Google Docs：字符级或词级 LCS
- 法律合同比对：精确到标点的差异检测
- 基因组比对：DNA 序列的 LCS 变体

## 效果评估

- 对 1000 行的源代码，LCS 在毫秒级完成
- Git 的 Myers 算法对典型提交（修改 < 10%）几乎瞬时使用
- 空间优化后，可处理数 MB 文件的比对

## 代码参考

- TypeScript: `examples/algorithms-ts/src/dynamic_programming.ts` → `longestCommonSubsequence()`
- Java: `examples/algorithms-java/LCS.java`
- Rust: `examples/algorithms/src/lcs.rs`
