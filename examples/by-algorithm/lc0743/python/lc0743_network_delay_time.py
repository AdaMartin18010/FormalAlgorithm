"""
LeetCode 743. Network Delay Time
链接: https://leetcode.com/problems/network-delay-time/
难度: Medium

题目描述:
有 n 个网络节点，标记为 1 到 n。给你一个列表 times，表示信号经过有向边的传递时间。
times[i] = (ui, vi, wi)，其中 ui 是源节点，vi 是目标节点，wi 是一个信号从源节点传递到目标节点的时间。
现在，从某个节点 K 发出一个信号。需要多久才能使所有节点都收到信号？如果不能使所有节点收到信号，返回 -1。

形式化规约:
  输入: G = (V, E), |V| = n, w(u,v) > 0, 源点 k
  输出: max_{v∈V} δ(k, v)，若存在不可达节点则返回 -1

最优解思路:
  Dijkstra 贪心算法。维护已确定最短距离的集合，每次从优先队列中
  取出当前距离估计最小的顶点，松弛其所有出边。

复杂度:
  时间: O((V + E) log V)
  空间: O(V + E)
"""

import heapq
from typing import List


class Solution:
    def networkDelayTime(self, times: List[List[int]], n: int, k: int) -> int:
        """
        Dijkstra 单源最短路径。时间 O((V+E) log V)，空间 O(V+E)。
        """
        # 建图（邻接表），转为 0-based
        graph = [[] for _ in range(n)]
        for u, v, w in times:
            graph[u - 1].append((v - 1, w))

        src = k - 1
        INF = float("inf")
        dist = [INF] * n
        visited = [False] * n
        dist[src] = 0

        heap = [(0, src)]
        while heap:
            d, u = heapq.heappop(heap)
            if visited[u]:
                continue
            visited[u] = True

            for v, w in graph[u]:
                if not visited[v] and dist[u] + w < dist[v]:
                    dist[v] = dist[u] + w
                    heapq.heappush(heap, (dist[v], v))

        max_dist = max(dist)
        return -1 if max_dist == INF else int(max_dist)


def test_network_delay_time():
    sol = Solution()

    # 示例 1
    assert sol.networkDelayTime([[2, 1, 1], [2, 3, 1], [3, 4, 1]], 4, 2) == 2
    # 示例 2
    assert sol.networkDelayTime([[1, 2, 1]], 2, 1) == 1
    # 不可达
    assert sol.networkDelayTime([[1, 2, 1]], 2, 2) == -1
    # 单节点
    assert sol.networkDelayTime([], 1, 1) == 0

    print("All tests passed for LC 743 - Network Delay Time")


if __name__ == "__main__":
    test_network_delay_time()
