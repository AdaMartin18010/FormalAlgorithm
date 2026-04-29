"""LeetCode 45. 跳跃游戏 II — Python 实现

给定一个长度为 n 的 0 索引整数数组 nums。初始位置为 nums[0]。
每个元素 nums[i] 表示从索引 i 向前跳转的最大长度。
返回到达 nums[n - 1] 的最小跳跃次数。假设你总是可以到达 nums[n - 1]。

对标: LeetCode 45 / docs/13-LeetCode算法面试专题/06-面试专题/03-高频Top100-DP与贪心.md
"""

from typing import List


def jump(nums: List[int]) -> int:
    """计算到达最后一个位置的最小跳跃次数。

    前置条件 (Pre):
        - nums 为非负整数数组，长度范围 [1, 10^4]。
        - 假设总是可以到达最后一个位置。

    后置条件 (Post):
        - 返回从索引 0 到达索引 n-1 的最小跳跃次数。

    核心思路:
        贪心法（BFS 思想）：将问题视为层序遍历，每次跳跃覆盖一层。
        维护当前层的最远覆盖范围 current_end 和下一层的最远覆盖范围 farthest。
        当遍历到 current_end 时，必须再进行一次跳跃，将 current_end 更新为 farthest。

    复杂度:
        时间复杂度: O(n) — 单次遍历。
        空间复杂度: O(1) — 仅使用常数额外变量。

    证明要点:
        - 引理：在区间 [0, current_end] 内，所有位置均可通过不超过 jumps 次跳跃到达。
        - 当遍历到 i <= current_end 时，farthest = max(farthest, i + nums[i])
          表示从当前层出发，下一层能到达的最远位置。
        - 当 i == current_end 时，必须进行一次新的跳跃才能超越 current_end。
          此时 jumps += 1，current_end = farthest，引理对下一层保持。
        - 由于假设可达，最终 current_end >= n-1，jumps 即为最小次数
          （每次跳跃都扩展到当前可能的最远位置，不会浪费跳跃次数）。

    Args:
        nums: 每个位置可跳跃的最大长度数组。

    Returns:
        到达最后一个位置的最小跳跃次数。
    """
    n = len(nums)
    if n <= 1:
        return 0

    jumps = 0
    current_end = 0
    farthest = 0

    for i in range(n - 1):
        farthest = max(farthest, i + nums[i])
        if i == current_end:
            jumps += 1
            current_end = farthest
            if current_end >= n - 1:
                break

    return jumps


if __name__ == "__main__":
    # LeetCode 官方示例
    assert jump([2, 3, 1, 1, 4]) == 2, "Example 1 failed"
    assert jump([2, 3, 0, 1, 4]) == 2, "Example 2 failed"

    # 边界条件
    assert jump([0]) == 0, "Single element"
    assert jump([1, 1]) == 1, "Two elements"
    assert jump([1, 2, 3]) == 2, "Minimum jumps"
    assert jump([5, 0, 0, 0, 0, 0]) == 1, "One big jump"
    assert jump([1, 1, 1, 1, 1]) == 4, "All ones"

    print("All tests passed.")
