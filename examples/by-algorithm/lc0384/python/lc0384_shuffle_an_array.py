"""LeetCode 384. 打乱数组 — Python 实现

实现 Fisher-Yates 洗牌算法，支持 reset 和 shuffle 操作。

对标: LeetCode 384
"""

import random
from typing import List


class Solution:
    """Fisher-Yates 洗牌算法。

    不变式：
        - self.original 保存初始数组。
        - self.nums 保存当前状态。

    复杂度:
        shuffle: 时间 O(n)，空间 O(1)（原地交换）
        reset:   时间 O(n)，空间 O(n)（返回副本）
    """

    def __init__(self, nums: List[int]):
        self.original = nums[:]
        self.nums = nums[:]

    def reset(self) -> List[int]:
        """将数组重置为初始状态并返回。"""
        self.nums = self.original[:]
        return self.nums

    def shuffle(self) -> List[int]:
        """使用 Fisher-Yates 算法打乱数组并返回结果。

        算法思路：
            从后往前遍历 i = n-1 .. 1，
            从 [0, i] 中随机选择 j 并交换 nums[i] 和 nums[j]。
            这样每个排列出现的概率均为 1/n!。
        """
        n = len(self.nums)
        for i in range(n - 1, 0, -1):
            j = random.randint(0, i)
            self.nums[i], self.nums[j] = self.nums[j], self.nums[i]
        return self.nums


if __name__ == "__main__":
    nums = [1, 2, 3]
    sol = Solution(nums)

    shuffled = sol.shuffle()
    assert sorted(shuffled) == [1, 2, 3], "Elements should match"

    assert sol.reset() == [1, 2, 3], "Reset failed"

    # 边界
    sol2 = Solution([])
    assert sol2.shuffle() == []
    assert sol2.reset() == []

    sol3 = Solution([5])
    assert sol3.shuffle() == [5]
    assert sol3.reset() == [5]

    print("All tests passed.")
