"""
LeetCode 9. Palindrome Number
链接: https://leetcode.com/problems/palindrome-number/
难度: Easy

题目描述:
给定一个整数 x，如果 x 是回文整数，返回 true；否则返回 false。
回文数是指正序（从左向右）和倒序（从右向左）读都是一样的整数。

形式化规约:
  输入: x ∈ Z
  输出: true  iff  x 的十进制表示是回文

最优解思路:
  反转一半数字：将数字的后半部分反转，与前半部分比较。
  避免将整个数字反转可能导致的溢出问题。

复杂度:
  时间: O(log₁₀ n)
  空间: O(1)

正确性要点:
  1. 负数不是回文数
  2. 以 0 结尾的数字（除 0 外）不是回文数
  3. 偶数位：前半 == 反转后半；奇数位：前半 == 反转后半 // 10
"""


class Solution:
    def isPalindrome(self, x: int) -> bool:
        """
        反转一半数字判断是否为回文数。
        """
        if x < 0:
            return False
        if x < 10:
            return True
        if x % 10 == 0:
            return False

        reversed_half = 0
        while x > reversed_half:
            reversed_half = reversed_half * 10 + x % 10
            x //= 10

        return x == reversed_half or x == reversed_half // 10


def test_is_palindrome():
    sol = Solution()
    # 示例 1
    assert sol.isPalindrome(121) is True
    # 示例 2
    assert sol.isPalindrome(-121) is False
    # 示例 3
    assert sol.isPalindrome(10) is False
    # 单个数字
    assert sol.isPalindrome(0) is True
    assert sol.isPalindrome(5) is True
    # 偶数位
    assert sol.isPalindrome(1221) is True
    assert sol.isPalindrome(1234) is False
    # 大回文数
    assert sol.isPalindrome(123454321) is True
    # 溢出风险数字
    assert sol.isPalindrome(2147483647) is False
    print("All tests passed for LC 9 - Palindrome Number")


if __name__ == "__main__":
    test_is_palindrome()
