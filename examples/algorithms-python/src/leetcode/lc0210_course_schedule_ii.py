"""
LeetCode 210. Course Schedule II
链接: https://leetcode.com/problems/course-schedule-ii/
难度: Medium

题目描述:
现在你总共有 numCourses 门课需要选，记为 0 到 numCourses - 1。
给你一个数组 prerequisites，其中 prerequisites[i] = [ai, bi]，表示在选修课程 ai 前必须先选修 bi。
返回一个为了完成所有课程所安排的学习顺序。如果不可能完成，返回空数组。

形式化规约:
  输入: numCourses, prerequisites
  输出: 一个合法的拓扑排序数组，若图非 DAG 则返回 []

最优解思路:
  Kahn 算法的直接扩展：在环检测的同时输出拓扑序。
  若输出顶点数等于 numCourses，则该顺序即为合法修课顺序。

复杂度:
  时间: O(V + E)
  空间: O(V + E)
"""

from typing import List
from collections import deque


class Solution:
    def findOrder(self, numCourses: int, prerequisites: List[List[int]]) -> List[int]:
        """
        Kahn 算法输出拓扑序。时间 O(V+E)，空间 O(V+E)。
        """
        n = numCourses
        adj = [[] for _ in range(n)]
        in_degree = [0] * n

        for ai, bi in prerequisites:
            adj[bi].append(ai)
            in_degree[ai] += 1

        queue = deque([i for i in range(n) if in_degree[i] == 0])
        result: List[int] = []

        while queue:
            node = queue.popleft()
            result.append(node)
            for neighbor in adj[node]:
                in_degree[neighbor] -= 1
                if in_degree[neighbor] == 0:
                    queue.append(neighbor)

        return result if len(result) == n else []


def test_find_order():
    sol = Solution()

    # 示例 1
    assert sol.findOrder(2, [[1, 0]]) == [0, 1]

    # 示例 2
    result2 = sol.findOrder(4, [[1, 0], [2, 0], [3, 1], [3, 2]])
    assert len(result2) == 4
    assert is_valid_order(4, [[1, 0], [2, 0], [3, 1], [3, 2]], result2)

    # 有环
    assert sol.findOrder(2, [[1, 0], [0, 1]]) == []

    # 无先修
    result4 = sol.findOrder(3, [])
    assert len(result4) == 3

    print("All tests passed for LC 210 - Course Schedule II")


def is_valid_order(n: int, prerequisites: List[List[int]], order: List[int]) -> bool:
    if len(order) != n:
        return False
    pos = {v: i for i, v in enumerate(order)}
    for ai, bi in prerequisites:
        if pos[ai] < pos[bi]:
            return False
    return True


if __name__ == "__main__":
    test_find_order()
