"""LeetCode 55. 跳跃游戏 — Python 实现

给定一个非负整数数组 nums，你最初位于数组的第一个下标。
数组中的每个元素代表你在该位置可以跳跃的最大长度。
判断你是否能够到达最后一个下标。

对标: LeetCode 55 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
"""

from typing import List


def can_jump(nums: List[int]) -> bool:
    """判断是否能到达最后一个下标。

    前置条件 (Pre):
        - nums 为非负整数数组，长度范围 [1, 10^4]。

    后置条件 (Post):
        - 若能从位置 0 到达位置 n-1，返回 True；否则返回 False。

    核心思路:
        贪心策略：维护当前能到达的最远位置 reach。
        遍历数组，若当前位置 i 在可达范围内（i <= reach），则更新最远位置。
        若遍历完成后 reach >= n-1，则可达。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(1) — 仅使用常数额外变量。

    证明要点:
        - 引理（可达区间单调性）：处理完位置 i 后，[0, reach] 均可从起点到达。
        - 若 i > reach，则位置 i 不可达，后续位置更不可达。
        - 最终 reach >= n-1 当且仅当最后一个位置可达。

    Args:
        nums: 每个位置可跳跃的最大长度数组。

    Returns:
        是否能到达最后一个下标。
    """
    reach = 0
    n = len(nums)

    for i in range(n):
        if i > reach:
            return False
        reach = max(reach, i + nums[i])
        if reach >= n - 1:
            return True

    return True


if __name__ == "__main__":
    # LeetCode 官方示例
    assert can_jump([2, 3, 1, 1, 4]) == True, "Example 1 failed"
    assert can_jump([3, 2, 1, 0, 4]) == False, "Example 2 failed"

    # 边界条件
    assert can_jump([0]) == True, "Single element"
    assert can_jump([1, 0]) == True, "Two elements reachable"
    assert can_jump([0, 1]) == False, "Two elements unreachable"
    assert can_jump([5, 0, 0, 0, 0, 0]) == True, "One big jump"
    assert can_jump([2, 0, 0]) == True, "Exact reach"

    print("All tests passed.")
