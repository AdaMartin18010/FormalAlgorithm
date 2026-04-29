"""LeetCode 370. 区间加法 — Python 实现

假设你有一个长度为 n 的数组，初始情况下所有的数字均为 0，
你将会被给出 k 个更新的操作。其中，每个操作会被表示为一个三元组：[startIndex, endIndex, inc]，
你需要将子数组 A[startIndex ... endIndex]（包括 startIndex 和 endIndex）增加 inc。

返回 k 次操作后的数组。

对标: LeetCode 370 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md
"""

from typing import List


def get_modified_array(length: int, updates: List[List[int]]) -> List[int]:
    """应用所有区间更新后返回最终数组。

    前置条件 (Pre):
        - length >= 1，表示数组初始长度。
        - updates 中每个元素为 [start, end, inc]，0 <= start <= end < length。

    后置条件 (Post):
        - 返回长度为 length 的数组，每个位置的值为覆盖该位置的所有更新的增量之和。

    核心思路:
        差分数组惰性更新：
        对区间 [l, r] 加 inc：diff[l] += inc，diff[r+1] -= inc。
        最后对 diff 求前缀和还原原数组。

    复杂度:
        时间复杂度: O(n + m) — m 为 updates 数量。
        空间复杂度: O(n) — 差分数组。

    证明要点:
        - 引理：单次差分更新后，前缀和还原仅在 [l, r] 范围内增加 inc。
        - 引理：差分更新具有线性叠加性。
        - 最终前缀和还原得到应用所有更新后的数组。

    Args:
        length: 数组长度。
        updates: 更新操作列表，每个元素为 [start, end, inc]。

    Returns:
        应用所有更新后的数组。
    """
    diff = [0] * length

    for start, end, inc in updates:
        diff[start] += inc
        if end + 1 < length:
            diff[end + 1] -= inc

    # 前缀和还原
    result = [0] * length
    result[0] = diff[0]
    for i in range(1, length):
        result[i] = result[i - 1] + diff[i]

    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    assert get_modified_array(5, [[1, 3, 2], [2, 4, 3], [0, 2, -2]]) == [-2, 0, 3, 5, 3], "Example 1 failed"

    # 边界条件
    assert get_modified_array(3, []) == [0, 0, 0], "No updates"
    assert get_modified_array(1, [[0, 0, 5]]) == [5], "Single element"
    assert get_modified_array(4, [[0, 3, 1]]) == [1, 1, 1, 1], "Full range update"
    assert get_modified_array(4, [[0, 0, 1], [3, 3, 2]]) == [1, 0, 0, 2], "Point updates"

    print("All tests passed.")
