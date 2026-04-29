"""LeetCode 39. 组合总和 — Python 实现

给定一个无重复元素的整数数组 candidates 和一个目标整数 target，找出 candidates 中可以使数字和为目标数 target 的所有不同组合。

每个数字可以被选取无限次。

对标: LeetCode 39 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md
"""

from typing import List


def combination_sum(candidates: List[int], target: int) -> List[List[int]]:
    """返回和为 target 的所有组合，同一数字可无限选取。

    前置条件 (Pre):
        - candidates 为互不相同的正整数数组。
        - 1 <= len(candidates) <= 30。
        - 1 <= candidates[i] <= 200。
        - 1 <= target <= 500。

    后置条件 (Post):
        - 返回所有和等于 target 的组合列表。
        - 每个组合为非降序排列（通过控制搜索起点保证）。
        - 结果不重复。

    回溯不变式 (Backtrack Invariant):
        - path 为当前已选数字列表，和为 curr_sum。
        - path 中的数字按非降序排列（通过 start 参数保证）。
        - curr_sum <= target。

    剪枝条件 (Pruning):
        - 若 curr_sum > target，剪枝（正整数保证后续只会更大）。
        - 若 curr_sum == target，记录解并返回。

    复杂度:
        时间复杂度: O(S) — S 为解空间树中所有可达状态数，最坏情况指数级。
        空间复杂度: O(target / min(candidates)) — 递归栈最深为 target 除以最小候选数。

    证明要点:
        - 不遗漏：从 start 开始枚举，允许重复选取同一元素，DFS 遍历了所有非降序的多重集组合。
        - 不重复：通过限制后续选取只能从当前索引开始，避免了 [2,3] 和 [3,2] 这样的重复排列。
        - 剪枝安全：所有候选数为正，curr_sum > target 时后续不可能回到 target，剪枝正确。

    Args:
        candidates: 互不相同的正整数数组。
        target: 目标和。

    Returns:
        所有和为 target 的组合列表。
    """
    result: List[List[int]] = []
    path: List[int] = []
    candidates.sort()

    def backtrack(start: int, curr_sum: int) -> None:
        if curr_sum == target:
            result.append(path.copy())
            return
        if curr_sum > target:
            return
        for i in range(start, len(candidates)):
            # 做选择
            path.append(candidates[i])
            backtrack(i, curr_sum + candidates[i])  # i 可重复选取
            # 撤销选择
            path.pop()

    backtrack(0, 0)
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert combination_sum([2, 3, 6, 7], 7) == [[2, 2, 3], [7]], "Example 1 failed"
    assert combination_sum([2, 3, 5], 8) == [
        [2, 2, 2, 2], [2, 3, 3], [3, 5]
    ], "Example 2 failed"
    assert combination_sum([2], 1) == [], "Example 3 failed"

    # 边界条件
    assert combination_sum([1], 1) == [[1]], "Single candidate single target"
    assert combination_sum([1], 2) == [[1, 1]], "Single candidate repeated"

    print("All tests passed.")
