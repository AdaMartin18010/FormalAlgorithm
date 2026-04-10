package dp;

import java.util.*;

/**
 * 背包问题 - 动态规划实现
 * 包含：0/1背包、完全背包、多重背包
 */
public class Knapsack {
    
    /**
     * 0/1背包问题 - 基础DP
     * 每件物品只能选一次
     * 时间复杂度: O(n * W)
     * 空间复杂度: O(W)
     */
    public static int knapsack01(int[] weights, int[] values, int capacity) {
        int n = weights.length;
        int[] dp = new int[capacity + 1];
        
        for (int i = 0; i < n; i++) {
            // 倒序遍历，保证每件物品只选一次
            for (int w = capacity; w >= weights[i]; w--) {
                dp[w] = Math.max(dp[w], dp[w - weights[i]] + values[i]);
            }
        }
        
        return dp[capacity];
    }
    
    /**
     * 0/1背包 - 返回选择的物品
     */
    public static Result knapsack01WithItems(int[] weights, int[] values, int capacity) {
        int n = weights.length;
        int[][] dp = new int[n + 1][capacity + 1];
        
        // 填充DP表
        for (int i = 1; i <= n; i++) {
            for (int w = 0; w <= capacity; w++) {
                if (weights[i - 1] <= w) {
                    dp[i][w] = Math.max(dp[i - 1][w], 
                                       dp[i - 1][w - weights[i - 1]] + values[i - 1]);
                } else {
                    dp[i][w] = dp[i - 1][w];
                }
            }
        }
        
        // 回溯找出选择的物品
        List<Integer> selectedItems = new ArrayList<>();
        int w = capacity;
        for (int i = n; i > 0 && w > 0; i--) {
            if (dp[i][w] != dp[i - 1][w]) {
                selectedItems.add(i - 1);
                w -= weights[i - 1];
            }
        }
        Collections.reverse(selectedItems);
        
        return new Result(dp[n][capacity], selectedItems);
    }
    
    /**
     * 完全背包问题
     * 每件物品可以选无限次
     */
    public static int unboundedKnapsack(int[] weights, int[] values, int capacity) {
        int n = weights.length;
        int[] dp = new int[capacity + 1];
        
        for (int i = 0; i < n; i++) {
            // 正序遍历，物品可以重复选择
            for (int w = weights[i]; w <= capacity; w++) {
                dp[w] = Math.max(dp[w], dp[w - weights[i]] + values[i]);
            }
        }
        
        return dp[capacity];
    }
    
    /**
     * 多重背包问题
     * 每件物品有数量限制
     */
    public static int boundedKnapsack(int[] weights, int[] values, int[] counts, int capacity) {
        int n = weights.length;
        int[] dp = new int[capacity + 1];
        
        for (int i = 0; i < n; i++) {
            // 二进制优化
            int count = counts[i];
            int k = 1;
            while (count > 0) {
                int use = Math.min(k, count);
                int weight = weights[i] * use;
                int value = values[i] * use;
                
                for (int w = capacity; w >= weight; w--) {
                    dp[w] = Math.max(dp[w], dp[w - weight] + value);
                }
                
                count -= use;
                k *= 2;
            }
        }
        
        return dp[capacity];
    }
    
    /**
     * 二维背包问题（重量和价值限制）
     */
    public static int twoDimensionKnapsack(int[] weights, int[] volumes, int[] values, 
                                           int maxWeight, int maxVolume) {
        int n = weights.length;
        int[][] dp = new int[maxWeight + 1][maxVolume + 1];
        
        for (int i = 0; i < n; i++) {
            for (int w = maxWeight; w >= weights[i]; w--) {
                for (int v = maxVolume; v >= volumes[i]; v--) {
                    dp[w][v] = Math.max(dp[w][v], 
                                       dp[w - weights[i]][v - volumes[i]] + values[i]);
                }
            }
        }
        
        return dp[maxWeight][maxVolume];
    }
    
    /**
     * 分组背包问题
     * 每组物品只能选一个
     */
    public static int groupKnapsack(int[][] groupWeights, int[][] groupValues, int capacity) {
        int[] dp = new int[capacity + 1];
        
        for (int g = 0; g < groupWeights.length; g++) {
            // 倒序遍历容量
            for (int w = capacity; w >= 0; w--) {
                // 枚举组内物品
                for (int i = 0; i < groupWeights[g].length; i++) {
                    if (w >= groupWeights[g][i]) {
                        dp[w] = Math.max(dp[w], dp[w - groupWeights[g][i]] + groupValues[g][i]);
                    }
                }
            }
        }
        
        return dp[capacity];
    }
    
    // 结果类
    public static class Result {
        public final int maxValue;
        public final List<Integer> selectedItems;
        
        Result(int maxValue, List<Integer> selectedItems) {
            this.maxValue = maxValue;
            this.selectedItems = selectedItems;
        }
    }
    
    // 测试
    public static void main(String[] args) {
        // 0/1背包测试
        int[] weights = {2, 3, 4, 5};
        int[] values = {3, 4, 5, 6};
        int capacity = 8;
        
        System.out.println("=== 0/1背包 ===");
        Result result = knapsack01WithItems(weights, values, capacity);
        System.out.println("最大价值: " + result.maxValue);
        System.out.println("选择物品: " + result.selectedItems);
        
        // 完全背包测试
        System.out.println("\n=== 完全背包 ===");
        int[] unboundedWeights = {1, 3, 4};
        int[] unboundedValues = {15, 20, 30};
        int unboundedCapacity = 10;
        System.out.println("最大价值: " + unboundedKnapsack(unboundedWeights, unboundedValues, unboundedCapacity));
        
        // 多重背包测试
        System.out.println("\n=== 多重背包 ===");
        int[] boundedWeights = {2, 3, 4};
        int[] boundedValues = {3, 4, 5};
        int[] counts = {2, 1, 3};
        int boundedCapacity = 10;
        System.out.println("最大价值: " + boundedKnapsack(boundedWeights, boundedValues, counts, boundedCapacity));
    }
}
