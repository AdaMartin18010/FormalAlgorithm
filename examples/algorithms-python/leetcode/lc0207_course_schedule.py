"""
LeetCode 207. Course Schedule
链接: https://leetcode.com/problems/course-schedule/
难度: Medium

算法: 拓扑排序（Kahn 算法）
时间复杂度: O(V + E)
空间复杂度: O(V + E)
"""

from typing import List
from collections import deque


class Solution:
    def canFinish(self, numCourses: int, prerequisites: List[List[int]]) -> bool:
        """
        判断是否能完成所有课程（即图是否为 DAG）。
        
        形式化规约:
        - 前置条件: numCourses >= 1，prerequisites 中课程编号有效
        - 后置条件: 返回 True 当且仅当图为有向无环图（DAG）
        
        算法: Kahn 拓扑排序。若最终处理的节点数 == V，则为 DAG。
        正确性核心: DAG 必有入度为 0 的节点；若算法终止后仍有未处理节点，则必有环。
        """
        # 构建邻接表和入度数组
        graph = [[] for _ in range(numCourses)]
        in_degree = [0] * numCourses
        
        for a, b in prerequisites:
            # b -> a，表示先修 b 才能修 a
            graph[b].append(a)
            in_degree[a] += 1
        
        # 将所有入度为 0 的节点入队
        queue = deque([i for i in range(numCourses) if in_degree[i] == 0])
        processed = 0
        
        while queue:
            u = queue.popleft()
            processed += 1
            for v in graph[u]:
                in_degree[v] -= 1
                if in_degree[v] == 0:
                    queue.append(v)
        
        return processed == numCourses


# ---------- 测试 ----------
if __name__ == "__main__":
    sol = Solution()
    
    # 测试用例 1: 无环
    num1, pre1 = 2, [[1, 0]]
    res1 = sol.canFinish(num1, pre1)
    print(f"Test 1: {res1} (expected: True)")
    assert res1 == True
    
    # 测试用例 2: 有环
    num2, pre2 = 2, [[1, 0], [0, 1]]
    res2 = sol.canFinish(num2, pre2)
    print(f"Test 2: {res2} (expected: False)")
    assert res2 == False
    
    # 测试用例 3: 多课程无环
    num3, pre3 = 4, [[1, 0], [2, 1], [3, 2]]
    res3 = sol.canFinish(num3, pre3)
    print(f"Test 3: {res3} (expected: True)")
    assert res3 == True
    
    print("\nAll tests passed!")
