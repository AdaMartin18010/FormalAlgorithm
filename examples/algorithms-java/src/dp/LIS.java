package dp;

import java.util.*;

/**
 * Longest Increasing Subsequence algorithms.
 */
public class LIS {

    /**
     * Returns the length of LIS using binary search (patience sorting).
     * Time complexity: O(n log n). Space complexity: O(n).
     */
    public static int length(int[] arr) {
        if (arr.length == 0) {
            return 0;
        }
        int[] tails = new int[arr.length];
        int size = 0;
        for (int x : arr) {
            int left = 0, right = size;
            while (left < right) {
                int mid = (left + right) >>> 1;
                if (tails[mid] < x) {
                    left = mid + 1;
                } else {
                    right = mid;
                }
            }
            tails[left] = x;
            if (left == size) {
                size++;
            }
        }
        return size;
    }

    /**
     * Returns the actual LIS sequence using dynamic programming.
     * Time complexity: O(n^2). Space complexity: O(n).
     */
    public static List<Integer> sequence(int[] arr) {
        int n = arr.length;
        if (n == 0) {
            return Collections.emptyList();
        }
        int[] dp = new int[n];
        int[] prev = new int[n];
        Arrays.fill(dp, 1);
        Arrays.fill(prev, -1);
        int maxLen = 1, maxIdx = 0;

        for (int i = 1; i < n; i++) {
            for (int j = 0; j < i; j++) {
                if (arr[j] < arr[i] && dp[j] + 1 > dp[i]) {
                    dp[i] = dp[j] + 1;
                    prev[i] = j;
                }
            }
            if (dp[i] > maxLen) {
                maxLen = dp[i];
                maxIdx = i;
            }
        }

        List<Integer> result = new ArrayList<>();
        for (int i = maxIdx; i >= 0; i = prev[i]) {
            result.add(arr[i]);
            if (prev[i] == -1) {
                break;
            }
        }
        Collections.reverse(result);
        return result;
    }
}
