"""LeetCode 338. 比特位计数 — Python 实现

给定一个整数 n，对于范围 [0, n] 中的每个数字 i，计算其二进制表示中 1 的个数，返回长度为 n+1 的数组。

对标: LeetCode 338 / docs/13-LeetCode算法面试专题/02-算法范式专题/11-位运算.md
"""

from typing import List


def count_bits(n: int) -> List[int]:
    """返回 [0, n] 中每个数字二进制 1 的个数。

    前置条件 (Pre):
        - 0 <= n <= 10^5。

    后置条件 (Post):
        - 返回长度为 n+1 的列表，ans[i] 为 i 的二进制中 1 的个数。

    DP 递推关系:
        - ans[0] = 0。
        - 对于 i > 0：ans[i] = ans[i >> 1] + (i & 1)。
        即：i 的 1 的个数等于右移一位后的 1 的个数加上最低位是否为 1。

    复杂度:
        时间复杂度: O(n) — 遍历 0 到 n 一次。
        空间复杂度: O(1) — 输出数组不计入，仅使用常数额外空间。

    证明要点:
        设 i 的二进制表示为 b_k b_{k-1} ... b_1 b_0。
        i >> 1 的二进制为 b_k b_{k-1} ... b_1，其 1 的个数为 popcount(i >> 1)。
        i & 1 = b_0。
        因此 popcount(i) = popcount(i >> 1) + b_0，递推正确。

    Args:
        n: 整数上限。

    Returns:
        [0, n] 各数二进制 1 的个数列表。
    """
    ans = [0] * (n + 1)
    for i in range(1, n + 1):
        ans[i] = ans[i >> 1] + (i & 1)
    return ans


def count_bits_alternative(n: int) -> List[int]:
    """另一种 DP 思路：ans[i] = ans[i & (i - 1)] + 1。

    i & (i - 1) 将 i 的最低位 1 清零，因此 ans[i] 比该数多一个 1。
    """
    ans = [0] * (n + 1)
    for i in range(1, n + 1):
        ans[i] = ans[i & (i - 1)] + 1
    return ans


if __name__ == "__main__":
    # LeetCode 官方示例
    assert count_bits(2) == [0, 1, 1], "Example 1 failed"
    assert count_bits(5) == [0, 1, 1, 2, 1, 2], "Example 2 failed"

    # 边界条件
    assert count_bits(0) == [0], "n=0"
    assert count_bits(1) == [0, 1], "n=1"
    assert count_bits(8) == [0, 1, 1, 2, 1, 2, 2, 3, 1], "n=8"

    # 验证两种方法结果一致
    for n in range(100):
        assert count_bits(n) == count_bits_alternative(n), f"Mismatch at n={n}"

    print("All tests passed.")
