"""
LeetCode 516. 最长回文子序列

给定一个字符串 s，找出其中最长的回文子序列，并返回该序列的长度。

思路：区间动态规划
- dp[i][j] 表示子串 s[i..j] 的最长回文子序列长度。
- 若 s[i] == s[j]，则 dp[i][j] = dp[i+1][j-1] + 2。
- 若 s[i] != s[j]，则 dp[i][j] = max(dp[i+1][j], dp[i][j-1])。
- 边界：dp[i][i] = 1。

时间复杂度：O(n^2)，空间复杂度：O(n^2)。
"""


def longest_palindrome_subseq(s: str) -> int:
    """计算字符串 s 的最长回文子序列长度。"""
    n = len(s)
    if n <= 1:
        return n

    # dp[i][j] = s[i..j] 的最长回文子序列长度
    dp = [[0] * n for _ in range(n)]
    for i in range(n):
        dp[i][i] = 1

    # 按区间长度从小到大枚举
    for length in range(2, n + 1):
        for i in range(n - length + 1):
            j = i + length - 1
            if s[i] == s[j]:
                dp[i][j] = 2 if length == 2 else dp[i + 1][j - 1] + 2
            else:
                dp[i][j] = max(dp[i + 1][j], dp[i][j - 1])

    return dp[0][n - 1]


# --- Tests ---
if __name__ == "__main__":
    assert longest_palindrome_subseq("bbbab") == 4
    assert longest_palindrome_subseq("cbbd") == 2
    assert longest_palindrome_subseq("a") == 1
    assert longest_palindrome_subseq("aaaa") == 4
    assert longest_palindrome_subseq("abc") == 1
    print("All tests passed for LC 516 - Longest Palindromic Subsequence")
