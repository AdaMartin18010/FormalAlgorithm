"""
LeetCode 647. Palindromic Substrings
链接: https://leetcode.com/problems/palindromic-substrings/
难度: Medium

题目描述:
给定一个字符串，计算这个字符串中有多少个回文子串。
具有不同开始位置或结束位置的子串，即使是由相同的字符组成，也会被视作不同的子串。

形式化规约:
  输入: s ∈ Σ*
  输出: 回文子串的数量

最优解思路:
  中心扩展法。每个回文子串都有一个中心（字符中心或间隙中心）。
  对于每个中心，向两边扩展，只要字符相等就计数。

复杂度:
  时间: O(n²)
  空间: O(1)

正确性要点:
  1. 2n-1 个中心覆盖所有奇偶长度的回文子串
  2. 每个中心向外扩展直到不匹配
  3. 每次扩展成功代表一个新的回文子串
"""


def count_substrings(s: str) -> int:
    """
    中心扩展法计数回文子串。
    时间复杂度 O(n²)，空间复杂度 O(1)。
    """
    n = len(s)
    count = 0

    for center in range(2 * n - 1):
        left = center // 2
        right = left + center % 2

        while left >= 0 and right < n and s[left] == s[right]:
            count += 1
            left -= 1
            right += 1

    return count


if __name__ == "__main__":
    # 示例 1: "a","b","c"
    assert count_substrings("abc") == 3, f"Example 1 failed: {count_substrings('abc')}"
    # 示例 2: "a","a","a","aa","aa","aaa"
    assert count_substrings("aaa") == 6, f"Example 2 failed: {count_substrings('aaa')}"
    # 边界: 空串
    assert count_substrings("") == 0, f"Empty failed: {count_substrings('')}"
    # 边界: 单字符
    assert count_substrings("a") == 1, f"Single char failed: {count_substrings('a')}"
    # 两个相同字符
    assert count_substrings("aa") == 3, f"Two same failed: {count_substrings('aa')}"
    # 两个不同字符
    assert count_substrings("ab") == 2, f"Two diff failed: {count_substrings('ab')}"
    # 偶回文
    assert count_substrings("abba") == 6, f"Even palindrome failed: {count_substrings('abba')}"

    print("All tests passed for LC 647 - Palindromic Substrings")
