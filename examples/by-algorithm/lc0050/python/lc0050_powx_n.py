"""
LeetCode 50. Pow(x, n)
链接: https://leetcode.com/problems/powx-n/
难度: Medium

题目描述:
实现 pow(x, n)，即计算 x 的 n 次幂（即 x^n）。

形式化规约:
  输入: x ∈ R, n ∈ Z
  输出: x^n

最优解思路:
  快速幂（二进制分解）：
  将 n 分解为二进制形式 n = Σ bᵢ · 2ⁱ，则 x^n = Π x^(2ⁱ)（对所有 bᵢ=1 的 i）。
  通过不断平方 base 并减半 exp 来累加结果。

复杂度:
  时间: O(log |n|)
  空间: O(1)

正确性要点:
  不变式: result · base^exp = x^n（原始值）
  1. 初始化：result=1, base=x, exp=n → 1·x^n = x^n
  2. 维护：exp 为奇数时 result *= base；然后 base *= base, exp //= 2
  3. 终止：exp = 0，result = x^n
"""


class Solution:
    def myPow(self, x: float, n: int) -> float:
        """
        快速幂计算 x^n。
        """
        if n == 0:
            return 1.0

        base = x
        exp = n
        result = 1.0

        if exp < 0:
            base = 1.0 / base
            exp = -exp

        while exp > 0:
            if exp % 2 == 1:
                result *= base
            base *= base
            exp //= 2

        return result


def test_my_pow():
    sol = Solution()
    # 示例 1
    assert abs(sol.myPow(2.0, 10) - 1024.0) < 1e-9
    # 示例 2
    assert abs(sol.myPow(2.1, 3) - 9.261) < 1e-3
    # 负指数
    assert abs(sol.myPow(2.0, -2) - 0.25) < 1e-9
    # 零指数
    assert abs(sol.myPow(0.0, 0) - 1.0) < 1e-9
    assert abs(sol.myPow(99.0, 0) - 1.0) < 1e-9
    # 负底数
    assert abs(sol.myPow(-2.0, 3) - (-8.0)) < 1e-9
    # 最小整数（不溢出）
    ans = sol.myPow(2.0, -2147483648)
    assert ans != float('inf') and ans >= 0
    print("All tests passed for LC 50 - Pow(x, n)")


if __name__ == "__main__":
    test_my_pow()
