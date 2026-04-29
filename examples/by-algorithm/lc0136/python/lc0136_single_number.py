"""LeetCode 136. 只出现一次的数字 — Python 实现

给定一个非空整数数组，除了某个元素只出现一次以外，其余每个元素均出现两次。找出那个只出现了一次的元素。

对标: LeetCode 136 / docs/13-LeetCode算法面试专题/02-算法范式专题/11-位运算.md
"""

from typing import List


def single_number(nums: List[int]) -> int:
    """返回数组中只出现一次的数字。

    前置条件 (Pre):
        - nums 非空。
        - 除一个元素外，其余每个元素均出现两次。

    后置条件 (Post):
        - 返回只出现一次的元素。

    核心性质:
        - 异或满足交换律和结合律：a ^ b = b ^ a，(a ^ b) ^ c = a ^ (b ^ c)。
        - 自反性：a ^ a = 0。
        - 单位元：a ^ 0 = a。

    复杂度:
        时间复杂度: O(n) — 遍历数组一次。
        空间复杂度: O(1) — 仅使用一个整型变量。

    证明要点:
        设只出现一次的元素为 x，其余元素成对出现。
        由于异或满足交换律和结合律，可将所有成对元素相邻：
        (a ^ a) ^ (b ^ b) ^ ... ^ x = 0 ^ 0 ^ ... ^ x = x。
        因此遍历异或的结果即为 x。

    Args:
        nums: 整数数组，除一个元素外其余均出现两次。

    Returns:
        只出现一次的元素。
    """
    result = 0
    for num in nums:
        result ^= num
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert single_number([2, 2, 1]) == 1, "Example 1 failed"
    assert single_number([4, 1, 2, 1, 2]) == 4, "Example 2 failed"
    assert single_number([1]) == 1, "Example 3 failed"

    # 边界条件
    assert single_number([0, 0, 7]) == 7, "With zero"
    assert single_number([-1, -1, 3]) == 3, "With negatives"
    assert single_number([100000, 100000, 42]) == 42, "Large numbers"

    print("All tests passed.")
