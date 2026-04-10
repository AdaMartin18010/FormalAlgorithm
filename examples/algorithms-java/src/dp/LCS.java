package dp;

import java.util.*;

/**
 * 最长公共子序列 (Longest Common Subsequence)
 * 时间复杂度: O(m * n)
 * 空间复杂度: O(m * n) 或优化到 O(min(m, n))
 */
public class LCS {
    
    /**
     * 计算LCS长度
     */
    public static int length(String s1, String s2) {
        int m = s1.length();
        int n = s2.length();
        int[][] dp = new int[m + 1][n + 1];
        
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }
        
        return dp[m][n];
    }
    
    /**
     * 计算LCS并返回序列
     */
    public static String findLCS(String s1, String s2) {
        int m = s1.length();
        int n = s2.length();
        int[][] dp = new int[m + 1][n + 1];
        
        // 填充DP表
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }
        
        // 回溯构造LCS
        StringBuilder lcs = new StringBuilder();
        int i = m, j = n;
        while (i > 0 && j > 0) {
            if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                lcs.append(s1.charAt(i - 1));
                i--;
                j--;
            } else if (dp[i - 1][j] > dp[i][j - 1]) {
                i--;
            } else {
                j--;
            }
        }
        
        return lcs.reverse().toString();
    }
    
    /**
     * 空间优化版本 - 只计算长度
     */
    public static int lengthOptimized(String s1, String s2) {
        // 确保s1是较短的字符串
        if (s1.length() > s2.length()) {
            String temp = s1;
            s1 = s2;
            s2 = temp;
        }
        
        int m = s1.length();
        int n = s2.length();
        int[] prev = new int[m + 1];
        int[] curr = new int[m + 1];
        
        for (int j = 1; j <= n; j++) {
            for (int i = 1; i <= m; i++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    curr[i] = prev[i - 1] + 1;
                } else {
                    curr[i] = Math.max(curr[i - 1], prev[i]);
                }
            }
            // 交换数组
            int[] temp = prev;
            prev = curr;
            curr = temp;
        }
        
        return prev[m];
    }
    
    /**
     * 获取所有LCS（可能有多个）
     */
    public static List<String> findAllLCS(String s1, String s2) {
        int m = s1.length();
        int n = s2.length();
        int[][] dp = new int[m + 1][n + 1];
        
        // 填充DP表
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }
        
        Set<String> result = new HashSet<>();
        StringBuilder current = new StringBuilder();
        findAllLCSDfs(s1, s2, dp, m, n, current, result);
        return new ArrayList<>(result);
    }
    
    private static void findAllLCSDfs(String s1, String s2, int[][] dp, 
                                       int i, int j, StringBuilder current, Set<String> result) {
        if (i == 0 || j == 0) {
            result.add(current.reverse().toString());
            current.reverse(); // 恢复
            return;
        }
        
        if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
            current.append(s1.charAt(i - 1));
            findAllLCSDfs(s1, s2, dp, i - 1, j - 1, current, result);
            current.deleteCharAt(current.length() - 1);
        } else {
            if (dp[i - 1][j] >= dp[i][j - 1]) {
                findAllLCSDfs(s1, s2, dp, i - 1, j, current, result);
            }
            if (dp[i][j - 1] >= dp[i - 1][j]) {
                findAllLCSDfs(s1, s2, dp, i, j - 1, current, result);
            }
        }
    }
    
    /**
     * 最长公共子串（连续）
     */
    public static String longestCommonSubstring(String s1, String s2) {
        int m = s1.length();
        int n = s2.length();
        int[][] dp = new int[m + 1][n + 1];
        int maxLength = 0;
        int endIndex = 0;
        
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                    if (dp[i][j] > maxLength) {
                        maxLength = dp[i][j];
                        endIndex = i;
                    }
                }
            }
        }
        
        return s1.substring(endIndex - maxLength, endIndex);
    }
    
    /**
     * 最短公共超序列 (Shortest Common Supersequence)
     */
    public static String shortestCommonSupersequence(String s1, String s2) {
        int m = s1.length();
        int n = s2.length();
        int[][] dp = new int[m + 1][n + 1];
        
        // 计算LCS
        for (int i = 1; i <= m; i++) {
            for (int j = 1; j <= n; j++) {
                if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                    dp[i][j] = dp[i - 1][j - 1] + 1;
                } else {
                    dp[i][j] = Math.max(dp[i - 1][j], dp[i][j - 1]);
                }
            }
        }
        
        // 构造SCS
        StringBuilder scs = new StringBuilder();
        int i = m, j = n;
        while (i > 0 && j > 0) {
            if (s1.charAt(i - 1) == s2.charAt(j - 1)) {
                scs.append(s1.charAt(i - 1));
                i--;
                j--;
            } else if (dp[i - 1][j] > dp[i][j - 1]) {
                scs.append(s1.charAt(i - 1));
                i--;
            } else {
                scs.append(s2.charAt(j - 1));
                j--;
            }
        }
        
        // 添加剩余字符
        while (i > 0) scs.append(s1.charAt(--i));
        while (j > 0) scs.append(s2.charAt(--j));
        
        return scs.reverse().toString();
    }
    
    // 测试
    public static void main(String[] args) {
        String s1 = "ABCDGH";
        String s2 = "AEDFHR";
        
        System.out.println("String 1: " + s1);
        System.out.println("String 2: " + s2);
        System.out.println("LCS Length: " + length(s1, s2));
        System.out.println("LCS: " + findLCS(s1, s2));
        System.out.println("All LCS: " + findAllLCS(s1, s2));
        
        String s3 = "ABABC";
        String s4 = "BABCA";
        System.out.println("\nLongest Common Substring of '" + s3 + "' and '" + s4 + "': " 
                          + longestCommonSubstring(s3, s4));
        
        System.out.println("Shortest Common Supersequence: " 
                          + shortestCommonSupersequence(s1, s2));
    }
}
