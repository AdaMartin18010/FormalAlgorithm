"""LeetCode 46. 全排列 — Python 实现

给定一个不含重复数字的数组 nums，返回其所有可能的全排列。

对标: LeetCode 46 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md
"""

from typing import List


def permute(nums: List[int]) -> List[List[int]]:
    """返回数组 nums 的所有全排列。

    前置条件 (Pre):
        - nums 为互不相同的整数数组。
        - 1 <= len(nums) <= 6。

    后置条件 (Post):
        - 返回列表包含 nums 的所有 n! 个排列，每个排列为长度为 n 的列表。
        - 结果不重复、不遗漏。

    回溯不变式 (Backtrack Invariant):
        设当前路径为 path，已使用元素集合为 used。
        - |path| + |used| 恒等于当前递归深度已处理的步数。
        - path 中元素互不相同，且均为 nums 中的元素。
        - 若 |path| = n，则 path 是 nums 的一个合法排列。

    复杂度:
        时间复杂度: O(n * n!) — 共 n! 个排列，每个排列复制代价 O(n)。
        空间复杂度: O(n) — 递归栈深度最多为 n，加上 path 和 used 的辅助空间。

    证明要点:
        - 不遗漏：每一步从所有未使用元素中选择一个加入 path，DFS 遍历了解空间树的全部 n! 条叶子路径。
        - 不重复：由于 nums 元素互异，且每层通过 used 集合保证同一元素不会在同一排列中出现两次，因此生成的排列两两不同。

    Args:
        nums: 互不相同的整数数组。

    Returns:
        包含所有全排列的列表。
    """
    n = len(nums)
    result: List[List[int]] = []
    path: List[int] = []
    used = [False] * n

    def backtrack() -> None:
        # 终止条件：path 长度达到 n，构成一个完整排列
        if len(path) == n:
            result.append(path.copy())
            return

        # 枚举所有可选元素
        for i in range(n):
            if used[i]:
                continue
            # 做选择
            used[i] = True
            path.append(nums[i])
            # 进入下一层决策树
            backtrack()
            # 撤销选择
            path.pop()
            used[i] = False

    backtrack()
    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert permute([1, 2, 3]) == [
        [1, 2, 3], [1, 3, 2], [2, 1, 3], [2, 3, 1], [3, 1, 2], [3, 2, 1]
    ], "Example 1 failed"

    assert permute([0, 1]) == [[0, 1], [1, 0]], "Example 2 failed"
    assert permute([1]) == [[1]], "Example 3 failed"

    # 边界条件
    assert len(permute([1, 2, 3, 4])) == 24, "4 elements should produce 24 permutations"

    print("All tests passed.")
