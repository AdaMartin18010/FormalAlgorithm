"""
LeetCode 204. Count Primes
链接: https://leetcode.com/problems/count-primes/
难度: Medium

题目描述:
给定整数 n，返回所有小于 n 的非负整数中质数的数量。

形式化规约:
  输入: n ∈ Z
  输出: |{p ∈ Z | 2 ≤ p < n 且 p 为质数}|

最优解思路:
  埃拉托斯特尼筛法（Sieve of Eratosthenes）。
  初始化所有数为质数，从 2 开始，将每个质数的倍数标记为合数。
  只需筛到 √n，因为任何合数 c < n 必有一个质因子 p ≤ √c < √n。

复杂度:
  时间: O(n log log n)
  空间: O(n)

正确性要点:
  1. 0 和 1 不是质数
  2. 从 i*i 开始标记，因为更小的倍数已被更小的质数标记
  3. 最终统计仍为 true 的个数
"""


def count_primes(n: int) -> int:
    """
    埃拉托斯特尼筛法计数质数。
    时间复杂度 O(n log log n)，空间复杂度 O(n)。
    """
    if n <= 2:
        return 0

    is_prime = [True] * n
    is_prime[0] = False
    is_prime[1] = False

    i = 2
    while i * i < n:
        if is_prime[i]:
            # 从 i*i 开始标记，步长为 i
            for j in range(i * i, n, i):
                is_prime[j] = False
        i += 1

    return sum(is_prime)


if __name__ == "__main__":
    # 示例 1: 小于 10 的质数有 4 个 (2,3,5,7)
    assert count_primes(10) == 4, f"Example 1 failed: {count_primes(10)}"
    # 示例 2
    assert count_primes(0) == 0, f"Example 2 failed: {count_primes(0)}"
    # 示例 3
    assert count_primes(1) == 0, f"Example 3 failed: {count_primes(1)}"
    # 边界: n 为质数
    assert count_primes(7) == 3, f"Prime n failed: {count_primes(7)}"
    # 较大值
    assert count_primes(100) == 25, f"100 failed: {count_primes(100)}"

    print("All tests passed for LC 204 - Count Primes")
