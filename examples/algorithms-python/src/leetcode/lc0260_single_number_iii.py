"""LeetCode 260. 只出现一次的数字 III — Python 实现

给定一个整数数组 nums，其中恰好有两个元素只出现一次，其余所有元素均出现两次。找出只出现一次的那两个元素。

对标: LeetCode 260 / docs/13-LeetCode算法面试专题/02-算法范式专题/11-位运算.md
"""

from typing import List


def single_number(nums: List[int]) -> List[int]:
    """返回数组中只出现一次的两个数字。

    前置条件 (Pre):
        - nums 非空。
        - 恰好有两个元素只出现一次，其余均出现两次。

    后置条件 (Post):
        - 返回包含两个只出现一次的元素的列表，顺序不限。

    核心思路:
        1. 全部异或得到 xor = a ^ b（a、b 为两个唯一元素）。
        2. xor != 0，因此至少有一位为 1。取最低位的 1（lsb = xor & -xor）。
        3. 该位上 a 和 b 必然不同。按该位是否为 1 将数组分为两组。
        4. 每组内分别异或，得到 a 和 b。

    复杂度:
        时间复杂度: O(n) — 遍历数组三次。
        空间复杂度: O(1) — 仅使用常数个变量。

    证明要点:
        - 步骤 1：由于成对元素异或为 0，全部异或后只剩 a ^ b。
        - 步骤 2：a != b 保证 xor != 0，存在区分位。
        - 步骤 3：按区分位分组后，a 和 b 分属不同组，成对元素在同一组（因为它们所有位相同）。
        - 步骤 4：每组内成对元素异或消去，分别得到 a 和 b。

    Args:
        nums: 整数数组，恰好有两个元素只出现一次。

    Returns:
        两个只出现一次的元素。
    """
    xor = 0
    for num in nums:
        xor ^= num

    # 取最低位的 1 作为区分位
    lsb = xor & -xor

    a, b = 0, 0
    for num in nums:
        if num & lsb:
            a ^= num
        else:
            b ^= num

    return [a, b]


if __name__ == "__main__":
    # LeetCode 官方示例
    result = single_number([1, 2, 1, 3, 2, 5])
    assert sorted(result) == [3, 5], f"Example 1 failed: {result}"

    result2 = single_number([-1, 0])
    assert sorted(result2) == [-1, 0], f"Example 2 failed: {result2}"

    result3 = single_number([0, 1])
    assert sorted(result3) == [0, 1], f"Example 3 failed: {result3}"

    print("All tests passed.")
