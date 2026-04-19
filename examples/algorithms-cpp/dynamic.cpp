/**
 * dynamic.cpp - C++动态规划算法实现
 * 包含：0/1背包、LIS长度、零钱问题
 */

#include <iostream>
#include <vector>
#include <algorithm>
#include <climits>
#include <cassert>

namespace dynamic {

int knapsack01(const std::vector<int>& weights, const std::vector<int>& values, int capacity) {
    int n = static_cast<int>(weights.size());
    std::vector<int> dp(capacity + 1, 0);
    for (int i = 0; i < n; ++i) {
        for (int c = capacity; c >= weights[i]; --c) {
            dp[c] = std::max(dp[c], dp[c - weights[i]] + values[i]);
        }
    }
    return dp[capacity];
}

int lisLength(const std::vector<int>& arr) {
    if (arr.empty()) return 0;
    std::vector<int> tails;
    for (int x : arr) {
        auto it = std::lower_bound(tails.begin(), tails.end(), x);
        if (it == tails.end()) tails.push_back(x);
        else *it = x;
    }
    return static_cast<int>(tails.size());
}

int coinChangeMin(const std::vector<int>& coins, int amount) {
    if (amount == 0) return 0;
    std::vector<int> dp(amount + 1, INT_MAX - 1);
    dp[0] = 0;
    for (int i = 1; i <= amount; ++i) {
        for (int coin : coins) {
            if (coin > 0 && coin <= i && dp[i - coin] != INT_MAX - 1) {
                dp[i] = std::min(dp[i], dp[i - coin] + 1);
            }
        }
    }
    return dp[amount] == INT_MAX - 1 ? -1 : dp[amount];
}

int coinChangeWays(const std::vector<int>& coins, int amount) {
    std::vector<int> dp(amount + 1, 0);
    dp[0] = 1;
    for (int coin : coins) {
        for (int i = coin; i <= amount; ++i) {
            dp[i] += dp[i - coin];
        }
    }
    return dp[amount];
}

} // namespace dynamic

int main() {
    using namespace dynamic;
    assert(knapsack01({2, 3, 4, 5}, {3, 4, 5, 6}, 5) == 7);
    assert(lisLength({10, 9, 2, 5, 3, 7, 101, 18}) == 4);
    assert(lisLength({}) == 0);
    assert(coinChangeMin({1, 2, 5}, 11) == 3);
    assert(coinChangeMin({2}, 3) == -1);
    assert(coinChangeWays({1, 2, 5}, 5) == 4);
    std::cout << "All dynamic programming tests passed!" << std::endl;
    return 0;
}
