"""
LeetCode 214. Shortest Palindrome
链接: https://leetcode.com/problems/shortest-palindrome/
难度: Hard

题目描述:
给定一个字符串 s，你可以通过在字符串前面添加字符将其转换为回文串。
返回你可以找到的最短回文串。

形式化规约:
  输入: s ∈ Σ*
  输出: 最短的字符串 t，使得 t + s 为回文串

最优解思路:
  KMP 前缀函数（π 数组）。
  构造字符串 s + "#" + reverse(s)，计算其前缀函数。
  最后一个值即为 s 的最长回文前缀长度。
  将剩余后缀反转后加到前面即可。

复杂度:
  时间: O(n)
  空间: O(n)

正确性要点:
  1. 回文前缀等价于该前缀等于 reverse(s) 的对应后缀
  2. KMP 前缀函数恰好计算了这种最长匹配
  3. 剩余部分必须全部反转添加，否则无法形成回文
"""


def shortest_palindrome(s: str) -> str:
    """
    使用 KMP 前缀函数找到最长回文前缀，然后将剩余部分反转加到前面。
    时间复杂度 O(n)，空间复杂度 O(n)。
    """
    if not s:
        return s

    rev = s[::-1]
    combined = s + "#" + rev
    n = len(combined)

    # 计算前缀函数
    pi = [0] * n
    for i in range(1, n):
        j = pi[i - 1]
        while j > 0 and combined[i] != combined[j]:
            j = pi[j - 1]
        if combined[i] == combined[j]:
            j += 1
        pi[i] = j

    prefix_len = pi[-1]
    return rev[: len(s) - prefix_len] + s


if __name__ == "__main__":
    # 示例 1
    assert shortest_palindrome("aacecaaa") == "aaacecaaa", f"Example 1 failed"
    # 示例 2
    assert shortest_palindrome("abcd") == "dcbabcd", f"Example 2 failed"
    # 边界: 空串
    assert shortest_palindrome("") == "", f"Empty failed"
    # 边界: 单字符
    assert shortest_palindrome("a") == "a", f"Single char failed"
    # 已经是回文
    assert shortest_palindrome("aba") == "aba", f"Already palindrome failed"
    assert shortest_palindrome("aa") == "aa", f"Even palindrome failed"

    print("All tests passed for LC 214 - Shortest Palindrome")
