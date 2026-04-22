"""LeetCode 137. 只出现一次的数字 II — Python 实现

给定一个整数数组，除了某个元素只出现一次以外，其余每个元素均出现了三次。找出那个只出现了一次的元素。

对标: LeetCode 137 / docs/13-LeetCode算法面试专题/02-算法范式专题/11-位运算.md
"""

from typing import List


def single_number(nums: List[int]) -> int:
    """返回数组中只出现一次的数字（其余出现三次）。

    前置条件 (Pre):
        - nums 非空。
        - 除一个元素外，其余每个元素均出现三次。

    后置条件 (Post):
        - 返回只出现一次的元素。

    状态机思路:
        对每一位，统计该位上 1 出现的次数模 3。
        - 出现 0 次：该位为 0。
        - 出现 1 次：该位为 1（来自唯一元素）。
        - 出现 3 次：该位为 0（模 3 后）。

        使用两个位掩码 ones 和 twos：
        - ones：记录到当前为止，哪些位上 1 出现了 1 次（模 3 意义下）。
        - twos：记录到当前为止，哪些位上 1 出现了 2 次（模 3 意义下）。

    复杂度:
        时间复杂度: O(n) — 遍历数组一次。
        空间复杂度: O(1) — 仅使用两个整型变量。

    证明要点:
        对于每个位，考虑所有数字在该位上的贡献：
        - 出现三次的数字在该位上贡献 3 个 1 或 0，模 3 后为 0。
        - 出现一次的数字在该位上贡献 1 个 1 或 0，模 3 后保留。
        因此最终 ones 即为唯一数字的位表示。

    Args:
        nums: 整数数组，除一个元素外其余均出现三次。

    Returns:
        只出现一次的元素。
    """
    ones, twos = 0, 0
    for num in nums:
        # 先更新 twos：当 ones 已有该位且当前 num 也有该位时，变为 2 次
        twos |= ones & num
        # 更新 ones：异或当前 num
        ones ^= num
        # 当某位在 ones 和 twos 中都为 1 时，说明出现了 3 次，需要清零
        threes = ones & twos
        ones &= ~threes
        twos &= ~threes
    return ones


if __name__ == "__main__":
    # LeetCode 官方示例
    assert single_number([2, 2, 3, 2]) == 3, "Example 1 failed"
    assert single_number([0, 1, 0, 1, 0, 1, 99]) == 99, "Example 2 failed"

    # 边界条件
    assert single_number([1, 1, 1, 2]) == 2, "Simple case"
    assert single_number([-2, -2, 1, -2]) == 1, "With negatives"
    assert single_number([42]) == 42, "Single element"

    print("All tests passed.")
