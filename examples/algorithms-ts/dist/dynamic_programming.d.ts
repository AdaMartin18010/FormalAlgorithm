/**
 * 动态规划算法集合
 */
/**
 * 0/1 背包问题
 * 时间复杂度: O(nW)
 * 空间复杂度: O(W)
 */
export declare function knapsack01(weights: number[], values: number[], capacity: number): number;
/**
 * 完全背包
 * 时间复杂度: O(nW)
 * 空间复杂度: O(W)
 */
export declare function unboundedKnapsack(weights: number[], values: number[], capacity: number): number;
/**
 * 最长递增子序列 (LIS) - 耐心排序 + 二分优化
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
export declare function longestIncreasingSubsequence(arr: number[]): number;
/**
 * 最长公共子序列 (LCS)
 * 时间复杂度: O(mn)
 * 空间复杂度: O(mn)
 */
export declare function longestCommonSubsequence(a: string, b: string): number;
/**
 * 零钱兑换（最小硬币数）
 * 时间复杂度: O(n * amount)
 * 空间复杂度: O(amount)
 */
export declare function coinChange(coins: number[], amount: number): number;
/**
 * 编辑距离 (Levenshtein Distance)
 * 时间复杂度: O(mn)
 * 空间复杂度: O(mn) 可优化至 O(min(m,n))
 */
export declare function editDistance(s: string, t: string): number;
/**
 * 矩阵链乘（最优括号化方案值）
 * 时间复杂度: O(n³)
 * 空间复杂度: O(n²)
 */
export declare function matrixChainOrder(dims: number[]): number;
export declare function runDynamicProgrammingTests(): void;
//# sourceMappingURL=dynamic_programming.d.ts.map