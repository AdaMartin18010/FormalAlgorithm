"""LeetCode 560. 和为 K 的子数组 — Python 实现

给定一个整数数组和一个整数 k，你需要找到该数组中和为 k 的连续的子数组的个数。

对标: LeetCode 560 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
"""

from typing import List


def subarray_sum(nums: List[int], k: int) -> int:
    """计算和为 k 的连续子数组的个数。

    前置条件 (Pre):
        - nums 为整数数组，长度范围 [1, 2·10^4]。
        - k 为整数，范围 [-10^7, 10^7]。

    后置条件 (Post):
        - 返回和恰好等于 k 的连续子数组的数量。

    核心思路:
        前缀和 + 哈希表：
        S(l, r) = prefix[r+1] - prefix[l] = k
        ⇔ prefix[r+1] = prefix[l] + k
        遍历过程中，用哈希表记录已出现的前缀和频次。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(n) — 哈希表最多存储 n+1 个前缀和。

    证明要点:
        - 引理：S(l, r) = prefix[r+1] - prefix[l]（前缀和定义）。
        - 引理：遍历到 i 时，哈希表包含 prefix[0..i] 的频次。
        - 查询 freq[prefix[i+1] - k] 即统计所有以 i 结尾且和为 k 的子数组数。
        - 累加结果即得全局计数。

    Args:
        nums: 输入整数数组。
        k: 目标和。

    Returns:
        和为 k 的连续子数组个数。
    """
    count = 0
    prefix = 0
    freq = {0: 1}  # 空前缀的和为 0，出现 1 次

    for num in nums:
        prefix += num
        # 若存在前缀和等于 prefix - k，则对应子数组和为 k
        count += freq.get(prefix - k, 0)
        freq[prefix] = freq.get(prefix, 0) + 1

    return count


if __name__ == "__main__":
    # LeetCode 官方示例
    assert subarray_sum([1, 1, 1], 2) == 2, "Example 1 failed"
    assert subarray_sum([1, 2, 3], 3) == 2, "Example 2 failed"

    # 边界条件
    assert subarray_sum([1], 1) == 1, "Single element match"
    assert subarray_sum([1], 0) == 0, "Single element no match"
    assert subarray_sum([0, 0, 0, 0, 0, 0, 0, 0, 0, 0], 0) == 55, "All zeros"
    assert subarray_sum([-1, -1, 1], 0) == 1, "Negative numbers"
    assert subarray_sum([1, -1, 0], 0) == 3, "Mixed numbers"

    print("All tests passed.")
