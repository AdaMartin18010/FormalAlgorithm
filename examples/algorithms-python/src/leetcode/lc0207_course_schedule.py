"""LeetCode 207. 课程表 — Python 实现

你这个学期必须选修 numCourses 门课程，记为 0 到 numCourses - 1。
在选修某些课程之前需要一些先修课程。先修课程按数组 prerequisites 给出，
其中 prerequisites[i] = [ai, bi] 表示如果要学习课程 ai 则必须先学习课程 bi。
请你判断是否可能完成所有课程的学习。

对标: LeetCode 207 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md
"""

from typing import List
from collections import deque


def can_finish(num_courses: int, prerequisites: List[List[int]]) -> bool:
    """判断是否能完成所有课程（检测有向图是否存在环）。

    前置条件 (Pre):
        - num_courses 范围 [1, 2000]，prerequisites 长度范围 [0, 5000]。
        - prerequisites[i] = [ai, bi] 表示 bi -> ai 的先修关系。

    后置条件 (Post):
        - 返回 True 当且仅当课程依赖图是无环的（即存在拓扑排序）。

    核心思路:
        拓扑排序（Kahn 算法 / BFS）：
        1. 计算每个节点的入度。
        2. 将所有入度为 0 的节点加入队列。
        3. 依次取出节点，将其邻接节点入度减 1；若邻接节点入度变为 0，入队。
        4. 若处理的节点数等于总节点数，则图无环。

    复杂度:
        时间复杂度: O(V + E) — V 为课程数，E 为先修关系数。
        空间复杂度: O(V + E) — 邻接表和入度数组。

    证明要点:
        - 引理：有向无环图（DAG）中至少存在一个入度为 0 的节点。
        - Kahn 算法每次移除一个入度为 0 的节点及其出边，剩余图仍为 DAG。
        - 若最终所有节点均被移除，原图为 DAG，存在拓扑排序，可以完成课程。
        - 若存在环，环上所有节点入度均 >= 1，永远不会入队，处理节点数 < V。

    Args:
        num_courses: 课程总数。
        prerequisites: 先修关系列表。

    Returns:
        是否能完成所有课程。
    """
    adj: List[List[int]] = [[] for _ in range(num_courses)]
    in_degree = [0] * num_courses

    for ai, bi in prerequisites:
        adj[bi].append(ai)
        in_degree[ai] += 1

    queue = deque([i for i in range(num_courses) if in_degree[i] == 0])
    processed = 0

    while queue:
        node = queue.popleft()
        processed += 1
        for neighbor in adj[node]:
            in_degree[neighbor] -= 1
            if in_degree[neighbor] == 0:
                queue.append(neighbor)

    return processed == num_courses


if __name__ == "__main__":
    # LeetCode 官方示例
    assert can_finish(2, [[1, 0]]) is True, "Example 1 failed"
    assert can_finish(2, [[1, 0], [0, 1]]) is False, "Example 2 failed"

    # 边界条件
    assert can_finish(1, []) is True, "Single course no prereq"
    assert can_finish(3, []) is True, "No prerequisites"
    assert can_finish(3, [[1, 0], [2, 1], [0, 2]]) is False, "Cycle of 3"
    assert can_finish(4, [[1, 0], [2, 0], [3, 1], [3, 2]]) is True, "DAG"

    print("All tests passed.")
