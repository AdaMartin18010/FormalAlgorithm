"""
LeetCode 239. Sliding Window Maximum
滑动窗口最大值

You are given an array of integers nums, there is a sliding window of size k
which is moving from the very left of the array to the very right.
You can only see the k numbers in the window.

Return the max sliding window.

使用单调递减双端队列维护窗口最大值
Use monotonically decreasing deque to maintain window maximum
"""

from collections import deque
from typing import List


class Solution:
    def maxSlidingWindow(self, nums: List[int], k: int) -> List[int]:
        """
        单调递减双端队列
        Monotonically decreasing deque

        deque stores indices, corresponding values are monotonically decreasing
        Time: O(n), Space: O(k)
        """
        dq: deque[int] = deque()  # 存储索引，对应值单调递减 / Store indices, values decreasing
        result: List[int] = []

        for i, num in enumerate(nums):
            # 移除队尾所有小于当前值的元素 / Remove smaller elements from tail
            while dq and nums[dq[-1]] < num:
                dq.pop()
            dq.append(i)

            # 移除已滑出窗口的队头元素 / Remove front elements out of window
            if dq[0] < i - k + 1:
                dq.popleft()

            # 窗口已形成，记录最大值 / Window formed, record max
            if i >= k - 1:
                result.append(nums[dq[0]])

        return result


# 简单测试 / Simple test
if __name__ == "__main__":
    sol = Solution()
    assert sol.maxSlidingWindow([1, 3, -1, -3, 5, 3, 6, 7], 3) == [3, 3, 5, 5, 6, 7]
    assert sol.maxSlidingWindow([1], 1) == [1]
    print("All tests passed!")
