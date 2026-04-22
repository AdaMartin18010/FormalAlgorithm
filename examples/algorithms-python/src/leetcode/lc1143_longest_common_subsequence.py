"""
LeetCode 1143. 最长公共子序列

给定两个字符串 text1 和 text2，返回这两个字符串的最长公共子序列的长度。
如果不存在公共子序列，返回 0。

思路：经典双串动态规划（空间优化）
- dp[j] 表示 text1[0..i) 与 text2[0..j) 的 LCS 长度。
- 若 text1[i-1] == text2[j-1]，则 dp[j] = prev + 1（prev 保存左上值）。
- 否则 dp[j] = max(dp[j], dp[j-1])。

时间复杂度：O(m*n)，空间复杂度：O(min(m, n))。
"""


def longest_common_subsequence(text1: str, text2: str) -> int:
    """计算两个字符串的最长公共子序列长度。"""
    m, n = len(text1), len(text2)
    if m == 0 or n == 0:
        return 0

    # 让 text2 指向较短的字符串，优化空间
    if m < n:
        text1, text2 = text2, text1
        m, n = n, m

    dp = [0] * (n + 1)

    for i in range(1, m + 1):
        prev = 0
        for j in range(1, n + 1):
            temp = dp[j]
            if text1[i - 1] == text2[j - 1]:
                dp[j] = prev + 1
            else:
                dp[j] = max(dp[j], dp[j - 1])
            prev = temp

    return dp[n]


# --- Tests ---
if __name__ == "__main__":
    assert longest_common_subsequence("abcde", "ace") == 3
    assert longest_common_subsequence("abc", "abc") == 3
    assert longest_common_subsequence("abc", "def") == 0
    assert longest_common_subsequence("", "abc") == 0
    assert longest_common_subsequence("bsbininm", "jmjkbkjkv") == 1
    print("All tests passed for LC 1143 - Longest Common Subsequence")
