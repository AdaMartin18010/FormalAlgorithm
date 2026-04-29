"""LeetCode 398. 随机数索引 — Python 实现

给定一个可能包含重复数字的整数数组，等概率随机返回目标数的索引。

对标: LeetCode 398
"""

import random
from typing import List


class Solution:
    """蓄水池抽样（Reservoir Sampling）。

    算法思路：
        遍历数组，遇到目标数时计数器 count 加 1。
        以 1/count 的概率选择当前索引作为结果。

    正确性证明（数学归纳法）：
        设目标数出现 m 次。
        基础：第 1 个目标数以概率 1 被选中（即 1/1）。
        归纳：假设前 k-1 个中每个被选中的概率为 1/(k-1)。
              第 k 个以 1/k 概率替换当前结果。
              前 k-1 个中某个被保留的概率 = (1/(k-1)) · ((k-1)/k) = 1/k。
        结论：m 次后每个目标数索引被选中的概率均为 1/m。

    复杂度:
        时间: O(n) 每次 pick
        空间: O(1)
    """

    def __init__(self, nums: List[int]):
        self.nums = nums

    def pick_index(self, target: int) -> int:
        count = 0
        result = -1
        for i, num in enumerate(self.nums):
            if num == target:
                count += 1
                # 以 1/count 的概率选择当前索引
                if random.randint(1, count) == 1:
                    result = i
        return result


if __name__ == "__main__":
    sol = Solution([1, 2, 3, 3, 3])

    # 测试 target=3 时只返回有效索引
    for _ in range(20):
        idx = sol.pick_index(3)
        assert idx in (2, 3, 4), f"Invalid index {idx}"

    assert sol.pick_index(1) == 0
    assert sol.pick_index(2) == 1

    # 概率分布测试
    freq = {}
    trials = 3000
    for _ in range(trials):
        idx = sol.pick_index(3)
        freq[idx] = freq.get(idx, 0) + 1

    for idx in (2, 3, 4):
        count = freq.get(idx, 0)
        assert 700 < count < 1300, f"Index {idx} frequency {count} out of range"

    print("All tests passed.")
