"""
LeetCode 28. Implement strStr()
链接: https://leetcode.com/problems/implement-strstr/
难度: Easy

题目描述:
给定两个字符串 haystack 和 needle，在 haystack 中找出 needle 第一个出现的位置（从 0 开始）。
如果不存在，则返回 -1。当 needle 为空字符串时返回 0。

形式化规约:
  输入: haystack ∈ Σ^n, needle ∈ Σ^m
  输出: min { i | 0 ≤ i ≤ n-m, haystack[i..i+m-1] = needle } 或 -1

最优解思路:
  KMP 算法：
  1. 计算 needle 的前缀函数（pi 数组），记录每个位置的最长相等前后缀长度
  2. 利用 pi 数组在 haystack 上进行线性匹配，失配时回跳到合适位置

复杂度:
  时间: O(n + m)
  空间: O(m)

正确性要点:
  1. pi 数组保证不回退 haystack 指针
  2. 失配时回跳到 pi[q-1] 继续匹配
  3. q == m 时找到匹配，返回 i + 1 - m
"""


class Solution:
    def strStr(self, haystack: str, needle: str) -> int:
        """
        KMP 算法实现 strStr。
        """
        if not needle:
            return 0
        n, m = len(haystack), len(needle)
        if n < m:
            return -1

        # 计算前缀函数 pi
        pi = [0] * m
        k = 0
        for q in range(1, m):
            while k > 0 and needle[k] != needle[q]:
                k = pi[k - 1]
            if needle[k] == needle[q]:
                k += 1
            pi[q] = k

        # KMP 匹配
        q = 0
        for i in range(n):
            while q > 0 and needle[q] != haystack[i]:
                q = pi[q - 1]
            if needle[q] == haystack[i]:
                q += 1
            if q == m:
                return i + 1 - m

        return -1


def test_str_str():
    sol = Solution()
    # 示例 1
    assert sol.strStr("hello", "ll") == 2
    # 示例 2
    assert sol.strStr("aaaaa", "bba") == -1
    # 空字符串
    assert sol.strStr("", "") == 0
    assert sol.strStr("hello", "") == 0
    assert sol.strStr("", "a") == -1
    # 重叠匹配
    assert sol.strStr("aaaa", "aa") == 0
    assert sol.strStr("abcabcabc", "abc") == 0
    # 不存在
    assert sol.strStr("abcdef", "gh") == -1
    assert sol.strStr("abc", "abcd") == -1
    # 单字符
    assert sol.strStr("a", "a") == 0
    assert sol.strStr("abc", "c") == 2
    print("All tests passed for LC 28 - Implement strStr()")


if __name__ == "__main__":
    test_str_str()
