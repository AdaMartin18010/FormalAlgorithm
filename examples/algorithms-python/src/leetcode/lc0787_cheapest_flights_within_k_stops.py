"""
LeetCode 787. Cheapest Flights Within K Stops
链接: https://leetcode.com/problems/cheapest-flights-within-k-stops/
难度: Medium

题目描述:
有 n 个城市通过一些航班连接。给你一个数组 flights ，其中 flights[i] = [fromi, toi, pricei] ，
表示该航班从城市 fromi 开始，以价格 pricei 抵达 toi。
现在给定所有的城市和航班，以及出发城市 src、目的地 dst 和最多允许中转次数 K，
返回从 src 到 dst 最便宜的价格。如果没有这样的路线，返回 -1。

形式化规约:
  输入: n 个城市, flights 列表, src, dst, K（最多中转次数）
  输出: 最多使用 K+1 条边的最短路径权重，若不存在则返回 -1

最优解思路:
  Bellman-Ford 的动态规划视角：dist_k[v] 表示最多使用 k 条边到达 v 的最小代价。
  进行 K+1 轮松弛，使用辅助数组防止同轮内的串联更新。

复杂度:
  时间: O(K * E)
  空间: O(V)
"""

from typing import List


class Solution:
    def findCheapestPrice(
        self, n: int, flights: List[List[int]], src: int, dst: int, k: int
    ) -> int:
        """
        Bellman-Ford K+1 轮松弛。时间 O(K * E)，空间 O(V)。
        """
        INF = float("inf")
        dist = [INF] * n
        dist[src] = 0

        # K+1 轮松弛（中转 K 次 = 最多 K+1 条边）
        for _ in range(k + 1):
            new_dist = dist.copy()
            for u, v, w in flights:
                if dist[u] + w < new_dist[v]:
                    new_dist[v] = dist[u] + w
            dist = new_dist

        return -1 if dist[dst] == INF else dist[dst]


def test_cheapest_price():
    sol = Solution()

    # 示例 1
    flights1 = [[0, 1, 100], [1, 2, 100], [2, 0, 100], [1, 3, 600], [2, 3, 200]]
    assert sol.findCheapestPrice(4, flights1, 0, 3, 1) == 700

    # 示例 2
    flights2 = [[0, 1, 100], [1, 2, 100], [0, 2, 500]]
    assert sol.findCheapestPrice(3, flights2, 0, 2, 1) == 200

    # 无路径
    assert sol.findCheapestPrice(2, [[0, 1, 100]], 1, 0, 0) == -1

    # 直达最便宜
    flights3 = [[0, 1, 100], [0, 1, 50]]
    assert sol.findCheapestPrice(2, flights3, 0, 1, 0) == 50

    print("All tests passed for LC 787 - Cheapest Flights Within K Stops")


if __name__ == "__main__":
    test_cheapest_price()
