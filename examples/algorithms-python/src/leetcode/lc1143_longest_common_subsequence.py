"""
LeetCode 1143. Longest Common Subsequence

Given two strings text1 and text2, return the length of their longest common
subsequence. If there is no common subsequence, return 0.

Approach: 2D DP with space-optimized 1D rolling array.
- dp[j] represents LCS length of text1[0..i-1] and text2[0..j-1].
- We keep prev (top-left) to handle the diagonal transition.

Time: O(m*n), Space: O(n)
"""


class Solution:
    def longestCommonSubsequence(self, text1: str, text2: str) -> int:
        m, n = len(text1), len(text2)
        # Ensure text2 is the shorter one for better space efficiency
        if m < n:
            text1, text2 = text2, text1
            m, n = n, m

        dp = [0] * (n + 1)

        for i in range(1, m + 1):
            prev = 0  # dp[i-1][j-1]
            for j in range(1, n + 1):
                temp = dp[j]  # dp[i-1][j] before overwrite
                if text1[i - 1] == text2[j - 1]:
                    dp[j] = prev + 1
                else:
                    dp[j] = max(dp[j], dp[j - 1])
                prev = temp

        return dp[n]


# --- Tests ---
if __name__ == "__main__":
    sol = Solution()
    assert sol.longestCommonSubsequence("abcde", "ace") == 3
    assert sol.longestCommonSubsequence("abc", "abc") == 3
    assert sol.longestCommonSubsequence("abc", "def") == 0
    assert sol.longestCommonSubsequence("", "abc") == 0
    assert sol.longestCommonSubsequence("bsbininm", "jmjkbkjkv") == 1
    print("All tests passed.")
