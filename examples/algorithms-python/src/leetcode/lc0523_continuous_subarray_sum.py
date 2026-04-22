"""LeetCode 523. 连续的子数组和 — Python 实现

给定一个整数数组和一个整数 k，检查数组中是否存在连续子数组的大小至少为 2，
且其和为 k 的倍数（即被 k 整除）。

对标: LeetCode 523 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
"""

from typing import List


def check_subarray_sum(nums: List[int], k: int) -> bool:
    """检查是否存在长度至少为 2 且和可被 k 整除的连续子数组。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [1, 10^5]。
        - k 为整数，范围 [-10^9, 10^9]。

    后置条件 (Post):
        - 若存在长度 >= 2 且和 % k == 0 的连续子数组，返回 True；否则返回 False。

    核心思路:
        前缀和 + 同余定理：
        k | S(l, r) ⇔ prefix[r+1] ≡ prefix[l] (mod k)
        维护哈希表记录每个余数最早出现的位置。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(min(n, |k|)) — 余数最多 |k| 种（k=0 时特判）。

    证明要点:
        - 引理：k | S(l, r) ⇔ prefix[r+1] ≡ prefix[l] (mod k)（同余定理）。
        - 引理：若相同余数在位置 i 和 j 出现（j > i），则子数组 nums[i..j-1] 的和可被 k 整除。
        - 哈希表存储余数最早出现位置，确保找到的子数组长度 >= 2。

    Args:
        nums: 输入整数数组。
        k: 模数。

    Returns:
        是否存在满足条件的连续子数组。
    """
    n = len(nums)
    if n < 2:
        return False

    # k = 0 特判：需要存在长度 >= 2 且和为 0 的子数组
    if k == 0:
        for i in range(n - 1):
            if nums[i] == 0 and nums[i + 1] == 0:
                return True
        return False

    prefix = 0
    # 余数 -> 最早出现的位置
    first_occurrence = {0: 0}  # prefix[0] = 0 出现在位置 0

    for i in range(n):
        prefix = (prefix + nums[i]) % k
        if prefix in first_occurrence:
            if i + 1 - first_occurrence[prefix] >= 2:
                return True
        else:
            first_occurrence[prefix] = i + 1

    return False


if __name__ == "__main__":
    # LeetCode 官方示例
    assert check_subarray_sum([23, 2, 4, 6, 7], 6) == True, "Example 1 failed"
    assert check_subarray_sum([23, 2, 6, 4, 7], 6) == True, "Example 2 failed"
    assert check_subarray_sum([23, 2, 6, 4, 7], 13) == False, "Example 3 failed"

    # 边界条件
    assert check_subarray_sum([0, 0], 0) == True, "Two zeros, k=0"
    assert check_subarray_sum([0], 0) == False, "Single element"
    assert check_subarray_sum([1, 2, 3], 10) == False, "No valid subarray"
    assert check_subarray_sum([1, 1], 2) == True, "Minimum length"
    assert check_subarray_sum([5, 0, 0, 0], 3) == True, "Zeros with k!=0"

    print("All tests passed.")
