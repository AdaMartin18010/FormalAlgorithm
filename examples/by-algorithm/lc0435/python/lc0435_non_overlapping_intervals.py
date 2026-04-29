"""LeetCode 435. 无重叠区间 — Python 实现

给定一个区间的集合 intervals，找到需要移除区间的最小数量，
使剩余区间互不重叠。

对标: LeetCode 435 / docs/13-LeetCode算法面试专题/02-算法范式专题/07-贪心算法.md
"""

from typing import List


def erase_overlap_intervals(intervals: List[List[int]]) -> int:
    """计算需要移除的最小区间数量，使剩余区间互不重叠。

    前置条件 (Pre):
        - intervals 为区间集合，每个区间为 [start, end)，1 <= len(intervals) <= 10^5。

    后置条件 (Post):
        - 返回需要移除的最小区间数量。

    核心思路:
        贪心策略：按结束时间排序，每次选择结束最早的且与已选区间不重叠的区间。
        结束越早的区间，留给后续区间的空间越大。

    复杂度:
        时间复杂度: O(n log n) — 排序主导。
        空间复杂度: O(1) — 忽略排序栈空间。

    证明要点:
        - 交换论证：设 g 为结束最早的区间。若最优解不包含 g，可将最优解中与 g 冲突的区间替换为 g，
          不减少解的数量。
        - 最优子结构：选择了 g 后，在结束时间晚于 g 的区间中求解子问题，其最优解与 g 组合即构成原问题最优解。

    Args:
        intervals: 区间集合，每个元素为 [start, end]。

    Returns:
        需要移除的最小区间数量。
    """
    if not intervals:
        return 0

    # 按结束时间排序
    intervals.sort(key=lambda x: x[1])

    count = 1  # 至少可以选第一个区间
    end = intervals[0][1]

    for i in range(1, len(intervals)):
        if intervals[i][0] >= end:
            count += 1
            end = intervals[i][1]

    return len(intervals) - count


if __name__ == "__main__":
    # LeetCode 官方示例
    assert erase_overlap_intervals([[1, 2], [2, 3], [3, 4], [1, 3]]) == 1, "Example 1 failed"
    assert erase_overlap_intervals([[1, 2], [1, 2], [1, 2]]) == 2, "Example 2 failed"
    assert erase_overlap_intervals([[1, 2], [2, 3]]) == 0, "Example 3 failed"

    # 边界条件
    assert erase_overlap_intervals([]) == 0, "Empty intervals"
    assert erase_overlap_intervals([[1, 2]]) == 0, "Single interval"
    assert erase_overlap_intervals([[1, 10], [2, 3], [4, 5], [6, 7]]) == 1, "One big interval"
    assert erase_overlap_intervals([[1, 100], [2, 3], [4, 5], [6, 7], [8, 9]]) == 1, "Multiple small"

    print("All tests passed.")
