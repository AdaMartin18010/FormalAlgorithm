/**
 * 动态规划算法集合
 */

import { runTests, assertEq, assertArrayEq, assertTrue } from "./utils";

/**
 * 0/1 背包问题
 * 时间复杂度: O(nW)
 * 空间复杂度: O(W)
 */
export function knapsack01(weights: number[], values: number[], capacity: number): number {
  const n = weights.length;
  const dp = new Array(capacity + 1).fill(0);
  for (let i = 0; i < n; i++) {
    for (let w = capacity; w >= weights[i]; w--) {
      dp[w] = Math.max(dp[w], dp[w - weights[i]] + values[i]);
    }
  }
  return dp[capacity];
}

/**
 * 完全背包
 * 时间复杂度: O(nW)
 * 空间复杂度: O(W)
 */
export function unboundedKnapsack(weights: number[], values: number[], capacity: number): number {
  const n = weights.length;
  const dp = new Array(capacity + 1).fill(0);
  for (let i = 0; i < n; i++) {
    for (let w = weights[i]; w <= capacity; w++) {
      dp[w] = Math.max(dp[w], dp[w - weights[i]] + values[i]);
    }
  }
  return dp[capacity];
}

/**
 * 最长递增子序列 (LIS) - 耐心排序 + 二分优化
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
export function longestIncreasingSubsequence(arr: number[]): number {
  if (arr.length === 0) return 0;
  const tails: number[] = [];
  for (const x of arr) {
    let l = 0, r = tails.length;
    while (l < r) {
      const m = Math.floor((l + r) / 2);
      if (tails[m] < x) l = m + 1;
      else r = m;
    }
    if (l === tails.length) tails.push(x);
    else tails[l] = x;
  }
  return tails.length;
}

/**
 * 最长公共子序列 (LCS)
 * 时间复杂度: O(mn)
 * 空间复杂度: O(mn)
 */
export function longestCommonSubsequence(a: string, b: string): number {
  const m = a.length, n = b.length;
  const dp: number[][] = Array.from({ length: m + 1 }, () => new Array(n + 1).fill(0));
  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      if (a[i - 1] === b[j - 1]) dp[i][j] = dp[i - 1][j - 1] + 1;
      else dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
    }
  }
  return dp[m][n];
}

/**
 * 零钱兑换（最小硬币数）
 * 时间复杂度: O(n * amount)
 * 空间复杂度: O(amount)
 */
export function coinChange(coins: number[], amount: number): number {
  const dp = new Array(amount + 1).fill(Infinity);
  dp[0] = 0;
  for (const coin of coins) {
    for (let x = coin; x <= amount; x++) {
      if (dp[x - coin] + 1 < dp[x]) dp[x] = dp[x - coin] + 1;
    }
  }
  return dp[amount] === Infinity ? -1 : dp[amount];
}

/**
 * 编辑距离 (Levenshtein Distance)
 * 时间复杂度: O(mn)
 * 空间复杂度: O(mn) 可优化至 O(min(m,n))
 */
export function editDistance(s: string, t: string): number {
  const m = s.length, n = t.length;
  const dp: number[][] = Array.from({ length: m + 1 }, () => new Array(n + 1).fill(0));
  for (let i = 0; i <= m; i++) dp[i][0] = i;
  for (let j = 0; j <= n; j++) dp[0][j] = j;
  for (let i = 1; i <= m; i++) {
    for (let j = 1; j <= n; j++) {
      if (s[i - 1] === t[j - 1]) dp[i][j] = dp[i - 1][j - 1];
      else dp[i][j] = 1 + Math.min(dp[i - 1][j], dp[i][j - 1], dp[i - 1][j - 1]);
    }
  }
  return dp[m][n];
}

/**
 * 矩阵链乘（最优括号化方案值）
 * 时间复杂度: O(n³)
 * 空间复杂度: O(n²)
 */
export function matrixChainOrder(dims: number[]): number {
  const n = dims.length - 1;
  const dp: number[][] = Array.from({ length: n }, () => new Array(n).fill(0));
  for (let len = 2; len <= n; len++) {
    for (let i = 0; i <= n - len; i++) {
      const j = i + len - 1;
      dp[i][j] = Infinity;
      for (let k = i; k < j; k++) {
        const cost = dp[i][k] + dp[k + 1][j] + dims[i] * dims[k + 1] * dims[j + 1];
        if (cost < dp[i][j]) dp[i][j] = cost;
      }
    }
  }
  return dp[0][n - 1];
}

export function runDynamicProgrammingTests(): void {
  runTests("DynamicProgramming", {
    "knapsack01": () => {
      assertEq(knapsack01([1, 3, 4, 5], [1, 4, 5, 7], 7), 9);
    },
    "unboundedKnapsack": () => {
      assertEq(unboundedKnapsack([1, 3, 4, 5], [1, 4, 5, 7], 7), 9); // 3+4=7 -> 4+5=9
    },
    "longestIncreasingSubsequence": () => {
      assertEq(longestIncreasingSubsequence([10, 9, 2, 5, 3, 7, 101, 18]), 4);
      assertEq(longestIncreasingSubsequence([0, 1, 0, 3, 2, 3]), 4);
    },
    "longestCommonSubsequence": () => {
      assertEq(longestCommonSubsequence("abcde", "ace"), 3);
      assertEq(longestCommonSubsequence("abc", "def"), 0);
    },
    "coinChange": () => {
      assertEq(coinChange([1, 2, 5], 11), 3);
      assertEq(coinChange([2], 3), -1);
      assertEq(coinChange([1], 0), 0);
    },
    "editDistance": () => {
      assertEq(editDistance("horse", "ros"), 3);
      assertEq(editDistance("intention", "execution"), 5);
    },
    "matrixChainOrder": () => {
      assertEq(matrixChainOrder([10, 30, 5, 60]), 4500);
    },
  });
}
