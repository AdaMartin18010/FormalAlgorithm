# 案例：最长递增子序列在股票价格分析中的应用

## 背景

在金融时间序列分析中，识别价格的**最长上升趋势**有助于量化交易策略的制定。最长递增子序列（Longest Increasing Subsequence, LIS）可以形式化地描述这一问题：给定一段时间内的每日收盘价，找出最长的严格递增价格序列。

## 问题定义

给定价格序列 $P = [p_1, p_2, ..., p_n]$，求最长的子序列 $P'$ 使得 $p'_{i} < p'_{i+1}$ 对所有 $i$ 成立。

## 动态规划解法

### $O(n^2)$ 基础 DP

设 $dp[i]$ 为以 $p_i$ 结尾的 LIS 长度：

$$dp[i] = 1 + \max_{j < i, p_j < p_i} dp[j]$$

### $O(n \log n)$ 优化（ patience sorting + 二分）

维护数组 $tails[k]$：长度为 $k$ 的递增子序列的最小末尾值。

对每个 $p_i$，在 $tails$ 中二分查找第一个 $> p_i$ 的位置并替换，若 $p_i$ 更大则追加。

## 金融意义

| 指标 | 解释 |
|------|------|
| LIS 长度 | 最长连续上升趋势的天数（允许跳过震荡日） |
| LIS 子序列 | 具体的买入-持有时间点序列 |
| tails 数组 | 不同长度趋势的最优"入场价" |

## 扩展：带权 LIS

将价格涨幅作为权重，求最大权重递增子序列，可用于优化收益而非单纯长度。

## 代码参考

- TypeScript: `examples/algorithms-ts/src/dynamic_programming.ts` → `longestIncreasingSubsequence()`
- Go: `examples/algorithms-go/dynamic.go` → `LIS` (若存在)
- Java: `examples/algorithms-java/LIS.java`

## 效果评估

- 对 10 年日频数据（~2500 点），$O(n \log n)$ 算法可在微秒级完成
- 结果可作为**趋势强度**的量化指标输入机器学习模型
