/**
 * dynamic.js - JavaScript动态规划算法实现
 * 包含：0/1背包、LIS长度、零钱问题
 */

class Dynamic {
    /**
     * 0/1背包问题
     * @param {number[]} weights - 重量数组
     * @param {number[]} values - 价值数组
     * @param {number} capacity - 容量
     * @returns {number} 最大价值
     */
    static knapsack01(weights, values, capacity) {
        const n = weights.length;
        const dp = new Array(capacity + 1).fill(0);
        for (let i = 0; i < n; i++) {
            for (let c = capacity; c >= weights[i]; c--) {
                dp[c] = Math.max(dp[c], dp[c - weights[i]] + values[i]);
            }
        }
        return dp[capacity];
    }

    /**
     * 最长递增子序列长度
     * @param {number[]} arr
     * @returns {number}
     */
    static lisLength(arr) {
        if (arr.length === 0) return 0;
        const tails = [];
        for (const x of arr) {
            let left = 0, right = tails.length;
            while (left < right) {
                const mid = Math.floor((left + right) / 2);
                if (tails[mid] < x) left = mid + 1;
                else right = mid;
            }
            tails[left] = x;
            if (left === tails.length) tails.push(x);
        }
        return tails.length;
    }

    /**
     * 零钱最小数量
     * @param {number[]} coins
     * @param {number} amount
     * @returns {number} 最小数量，不可能返回 -1
     */
    static coinChangeMin(coins, amount) {
        if (amount === 0) return 0;
        const INF = Number.MAX_SAFE_INTEGER - 1;
        const dp = new Array(amount + 1).fill(INF);
        dp[0] = 0;
        for (let i = 1; i <= amount; i++) {
            for (const coin of coins) {
                if (coin > 0 && coin <= i && dp[i - coin] !== INF) {
                    dp[i] = Math.min(dp[i], dp[i - coin] + 1);
                }
            }
        }
        return dp[amount] === INF ? -1 : dp[amount];
    }

    /**
     * 零钱组合数
     */
    static coinChangeWays(coins, amount) {
        const dp = new Array(amount + 1).fill(0);
        dp[0] = 1;
        for (const coin of coins) {
            for (let i = coin; i <= amount; i++) {
                dp[i] += dp[i - coin];
            }
        }
        return dp[amount];
    }
}

// 简单测试
function assertEq(name, expected, actual) {
    if (expected !== actual) throw new Error(`FAIL ${name}: expected ${expected}, got ${actual}`);
}

function runTests() {
    assertEq("Knapsack", 7, Dynamic.knapsack01([2, 3, 4, 5], [3, 4, 5, 6], 5));
    assertEq("LIS", 4, Dynamic.lisLength([10, 9, 2, 5, 3, 7, 101, 18]));
    assertEq("LIS empty", 0, Dynamic.lisLength([]));
    assertEq("CoinMin", 3, Dynamic.coinChangeMin([1, 2, 5], 11));
    assertEq("CoinImpossible", -1, Dynamic.coinChangeMin([2], 3));
    assertEq("CoinWays", 4, Dynamic.coinChangeWays([1, 2, 5], 5));
    console.log("All dynamic programming tests passed!");
}

runTests();

module.exports = { Dynamic };
