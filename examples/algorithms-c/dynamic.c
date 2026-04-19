/**
 * dynamic.c - C语言动态规划算法实现
 * 包含：0/1背包、LIS长度、零钱问题
 */

#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <assert.h>
#include <limits.h>

int knapsack_01(const int weights[], const int values[], int n, int capacity) {
    int* dp = (int*)calloc(capacity + 1, sizeof(int));
    for (int i = 0; i < n; i++) {
        for (int c = capacity; c >= weights[i]; c--) {
            int new_val = dp[c - weights[i]] + values[i];
            if (new_val > dp[c]) dp[c] = new_val;
        }
    }
    int result = dp[capacity];
    free(dp);
    return result;
}

int lis_length(const int arr[], int n) {
    if (n == 0) return 0;
    int* tails = (int*)malloc(n * sizeof(int));
    int size = 0;
    for (int i = 0; i < n; i++) {
        int left = 0, right = size;
        while (left < right) {
            int mid = left + (right - left) / 2;
            if (tails[mid] < arr[i]) left = mid + 1;
            else right = mid;
        }
        tails[left] = arr[i];
        if (left == size) size++;
    }
    free(tails);
    return size;
}

int coin_change_min(const int coins[], int n, int amount) {
    if (amount == 0) return 0;
    int* dp = (int*)malloc((amount + 1) * sizeof(int));
    for (int i = 0; i <= amount; i++) dp[i] = INT_MAX - 1;
    dp[0] = 0;
    for (int i = 1; i <= amount; i++) {
        for (int j = 0; j < n; j++) {
            int coin = coins[j];
            if (coin > 0 && coin <= i && dp[i - coin] != INT_MAX - 1) {
                int new_val = dp[i - coin] + 1;
                if (new_val < dp[i]) dp[i] = new_val;
            }
        }
    }
    int result = dp[amount] == INT_MAX - 1 ? -1 : dp[amount];
    free(dp);
    return result;
}

int coin_change_ways(const int coins[], int n, int amount) {
    int* dp = (int*)calloc(amount + 1, sizeof(int));
    dp[0] = 1;
    for (int j = 0; j < n; j++) {
        for (int i = coins[j]; i <= amount; i++) {
            dp[i] += dp[i - coins[j]];
        }
    }
    int result = dp[amount];
    free(dp);
    return result;
}

int main() {
    int weights[] = {2, 3, 4, 5};
    int values[] = {3, 4, 5, 6};
    assert(knapsack_01(weights, values, 4, 5) == 7);
    
    int arr[] = {10, 9, 2, 5, 3, 7, 101, 18};
    assert(lis_length(arr, 8) == 4);
    assert(lis_length(NULL, 0) == 0);
    
    int coins[] = {1, 2, 5};
    assert(coin_change_min(coins, 3, 11) == 3);
    assert(coin_change_min(coins, 3, 3) == 2);
    assert(coin_change_ways(coins, 3, 5) == 4);
    
    printf("All dynamic programming tests passed!\n");
    return 0;
}
