"""LeetCode 239. 滑动窗口最大值 — Python 实现

给你一个整数数组 nums，有一个大小为 k 的滑动窗口从数组的最左侧移动到最右侧。
只可以看到窗口中的 k 个数字，返回滑动窗口中的最大值。

对标: LeetCode 239 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
"""

from typing import List
from collections import deque


def max_sliding_window(nums: List[int], k: int) -> List[int]:
    """计算每个滑动窗口中的最大值。

    前置条件 (Pre):
        - nums 为整数数组，长度 ∈ [1, 10^5]。
        - k ∈ [1, len(nums)]，nums[i] ∈ [-10^4, 10^4]。

    后置条件 (Post):
        - 返回长度为 n - k + 1 的数组，其中 result[i] = max(nums[i..i+k-1])。

    算法框架:
        单调队列优化：维护一个双端队列，存储窗口中可能成为最大值的元素的索引。
        队列中的索引对应的值单调递减。

    窗口不变式 WindowInvariant(left, right):
        deque 中存储的索引均落在当前窗口 [right-k+1, right] 内。
        deque 中对应的值严格单调递减：
            nums[deque[0]] > nums[deque[1]] > ... > nums[deque[-1]]

        维护：
        - 初始队列为空。
        - 扩展 right：
          * 从队尾弹出所有满足 nums[deque[-1]] ≤ nums[right] 的索引
            （这些元素不可能成为未来窗口的最大值）。
          * 将 right 入队。
          * 若 deque[0] 已不在当前窗口内（deque[0] ≤ right - k），从队首弹出。
        - 当窗口形成后（right ≥ k-1），deque[0] 即为当前窗口最大值。

    复杂度:
        时间复杂度: O(n) — 摊还分析：每个元素最多入队一次、出队一次。
        空间复杂度: O(k) — 队列最多存储 k 个索引。

    证明要点:
        - 单调队列正确性见 docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md
        - 核心：队首始终为当前窗口最大值；队尾淘汰策略保证任何被移出的元素
          不可能成为后续窗口的最大值。

    Args:
        nums: 整数数组。
        k: 滑动窗口大小。

    Returns:
        每个窗口位置对应的最大值数组。
    """
    if not nums or k == 0:
        return []

    n = len(nums)
    result: List[int] = []
    dq: deque[int] = deque()

    for right in range(n):
        # 移除队尾不大于当前值的元素（它们不可能成为后续窗口的最大值）
        while dq and nums[dq[-1]] <= nums[right]:
            dq.pop()

        dq.append(right)

        # 移除队首不在窗口内的元素
        if dq[0] <= right - k:
            dq.popleft()

        # 窗口已形成，记录最大值
        if right >= k - 1:
            result.append(nums[dq[0]])

    return result


if __name__ == "__main__":
    # 示例 1
    assert max_sliding_window([1, 3, -1, -3, 5, 3, 6, 7], 3) == [3, 3, 5, 5, 6, 7], "Example 1 failed"

    # 示例 2
    assert max_sliding_window([1], 1) == [1], "Example 2 failed"

    # 边界：k == n
    assert max_sliding_window([1, 2, 3, 4], 4) == [4], "k equals n"

    # 边界：递增数组
    assert max_sliding_window([1, 2, 3, 4, 5], 2) == [2, 3, 4, 5], "Increasing"

    # 边界：递减数组
    assert max_sliding_window([5, 4, 3, 2, 1], 2) == [5, 4, 3, 2], "Decreasing"

    # 边界：全相同
    assert max_sliding_window([5, 5, 5, 5], 2) == [5, 5, 5], "All same"

    # 边界：负数
    assert max_sliding_window([-1, -3, -5, -2], 2) == [-1, -3, -2], "Negative"

    print("All tests passed.")
