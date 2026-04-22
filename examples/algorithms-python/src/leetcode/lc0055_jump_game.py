"""LeetCode 55. 跳跃游戏 — Python 实现

给定一个非负整数数组 nums，你最初位于数组的第一个下标。
数组中的每个元素代表你在该位置可以跳跃的最大长度。
判断你是否能够到达最后一个下标。

对标: LeetCode 55 / docs/13-LeetCode算法面试专题/06-面试专题/03-高频Top100-DP与贪心.md
"""

from typing import List


def can_jump(nums: List[int]) -> bool:
    """判断是否能从第一个位置跳到最后一个位置。

    前置条件 (Pre):
        - nums 为非负整数数组，长度范围 [1, 10^4]。
        - nums[i] 范围 [0, 10^5]。

    后置条件 (Post):
        - 返回 True 当且仅当存在一条从索引 0 到索引 n-1 的合法跳跃路径。

    核心思路:
        贪心法：维护最远可达位置 max_reach。
        遍历数组，若当前索引 i <= max_reach，则可以到达 i，
        并更新 max_reach = max(max_reach, i + nums[i])。
        若某时刻 max_reach >= n-1，返回 True；若 i > max_reach，返回 False。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(1) — 仅使用常数额外变量。

    证明要点:
        - 引理：max_reach 始终等于从起点出发经过不超过 i 步能到达的最远位置。
        - 若 i <= max_reach，则 i 可达；从 i 跳跃可到达 i + nums[i]，
          因此更新 max_reach 保持引理。
        - 若 max_reach >= n-1，则终点可达。
        - 若 i > max_reach，则 i 不可达，后续所有位置均不可达（数组非负，
          无法从前面位置跳过 i 到达更后面）。

    Args:
        nums: 每个位置可跳跃的最大长度数组。

    Returns:
        是否能到达最后一个下标。
    """
    max_reach = 0
    n = len(nums)
    for i in range(n):
        if i > max_reach:
            return False
        max_reach = max(max_reach, i + nums[i])
        if max_reach >= n - 1:
            return True
    return True


if __name__ == "__main__":
    # LeetCode 官方示例
    assert can_jump([2, 3, 1, 1, 4]) is True, "Example 1 failed"
    assert can_jump([3, 2, 1, 0, 4]) is False, "Example 2 failed"

    # 边界条件
    assert can_jump([0]) is True, "Single element"
    assert can_jump([1, 0]) is True, "Two elements reachable"
    assert can_jump([0, 1]) is False, "Two elements unreachable"
    assert can_jump([2, 0, 0]) is True, "Skip over zero"
    assert can_jump([1, 1, 1, 1, 1]) is True, "All ones"

    # 大规模测试
    large_nums = [1000] * 1000
    assert can_jump(large_nums) is True, "Large reachable"

    print("All tests passed.")
