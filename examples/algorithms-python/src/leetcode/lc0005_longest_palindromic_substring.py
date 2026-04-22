"""
LeetCode 5. Longest Palindromic Substring
链接: https://leetcode.com/problems/longest-palindromic-substring/
难度: Medium

题目描述:
给定一个字符串 s，找到 s 中最长的回文子串。

形式化规约:
  输入: s ∈ Σ^n
  输出: 子串 s[l..r] 满足 s[l..r] = reverse(s[l..r]) 且长度最大

最优解思路:
  中心扩展法：枚举 2n-1 个中心（字符中心和间隙中心），向两侧扩展直到不再回文。
  记录最长回文子串的起始位置和长度。

复杂度:
  时间: O(n^2)
  空间: O(1)

正确性要点:
  1. 奇数长度回文的中心是单个字符
  2. 偶数长度回文的中心是两个字符之间的间隙
  3. 每次扩展后更新最长记录
"""


class Solution:
    def longestPalindrome(self, s: str) -> str:
        """
        中心扩展法寻找最长回文子串。
        """
        n = len(s)
        if n == 0:
            return ""

        start, max_len = 0, 1

        def expand_around_center(left: int, right: int) -> int:
            """从 left, right 向两侧扩展，返回回文长度。"""
            while left >= 0 and right < n and s[left] == s[right]:
                left -= 1
                right += 1
            return right - left - 1

        for i in range(n):
            len1 = expand_around_center(i, i)       # 奇数长度
            len2 = expand_around_center(i, i + 1)   # 偶数长度
            length = max(len1, len2)
            if length > max_len:
                max_len = length
                start = i - (length - 1) // 2

        return s[start:start + max_len]


def test_longest_palindrome():
    sol = Solution()
    # 示例 1
    assert sol.longestPalindrome("babad") in ("bab", "aba")
    # 示例 2
    assert sol.longestPalindrome("cbbd") == "bb"
    # 单个字符
    assert sol.longestPalindrome("a") == "a"
    # 全部相同
    assert sol.longestPalindrome("aaaa") == "aaaa"
    # 无重复字符
    assert sol.longestPalindrome("abc") in ("a", "b", "c")
    # 较长回文
    assert sol.longestPalindrome("forgeeksskeegfor") == "geeksskeeg"
    print("All tests passed for LC 5 - Longest Palindromic Substring")


if __name__ == "__main__":
    test_longest_palindrome()
