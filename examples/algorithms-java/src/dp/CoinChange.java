package dp;

/**
 * Coin change problem algorithms.
 */
public class CoinChange {

    /**
     * Returns the minimum number of coins to make amount, or -1 if impossible.
     * Time complexity: O(n * amount). Space complexity: O(amount).
     */
    public static int minCoins(int[] coins, int amount) {
        if (amount == 0) {
            return 0;
        }
        int[] dp = new int[amount + 1];
        java.util.Arrays.fill(dp, Integer.MAX_VALUE - 1);
        dp[0] = 0;
        for (int i = 1; i <= amount; i++) {
            for (int coin : coins) {
                if (coin > 0 && coin <= i && dp[i - coin] != Integer.MAX_VALUE - 1) {
                    dp[i] = Math.min(dp[i], dp[i - coin] + 1);
                }
            }
        }
        return dp[amount] == Integer.MAX_VALUE - 1 ? -1 : dp[amount];
    }

    /**
     * Returns the number of ways to make amount.
     * Time complexity: O(n * amount). Space complexity: O(amount).
     */
    public static int ways(int[] coins, int amount) {
        int[] dp = new int[amount + 1];
        dp[0] = 1;
        for (int coin : coins) {
            for (int i = coin; i <= amount; i++) {
                dp[i] += dp[i - coin];
            }
        }
        return dp[amount];
    }
}
