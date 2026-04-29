"""
LeetCode 133. Clone Graph
链接: https://leetcode.com/problems/clone-graph/
难度: Medium

题目描述:
给你无向连通图中一个节点的引用，请你返回该图的深拷贝。

形式化规约:
  输入: 连通无向图 G = (V, E) 的一个节点的引用, |V| ∈ [1, 100]
  输出: G' ≅ G 的一个节点的引用, 且 V' ∩ V = ∅

最优解思路:
  DFS/BFS + 哈希映射（引用不变式）：
  使用字典维护 "原节点 → 新节点" 的映射，防止环导致的无限递归。
  每个原节点仅被复制一次。

复杂度:
  时间: O(V + E)
  空间: O(V)
"""

from typing import Optional


class Node:
    def __init__(self, val: int = 0, neighbors: Optional[list["Node"]] = None):
        self.val = val
        self.neighbors = neighbors if neighbors is not None else []


class Solution:
    def cloneGraph(self, node: Optional["Node"]) -> Optional["Node"]:
        """
        DFS 深拷贝图。时间 O(V+E)，空间 O(V)。
        """
        if node is None:
            return None

        visited: dict[int, Node] = {}

        def dfs(n: Node) -> Node:
            if n.val in visited:
                return visited[n.val]

            # 立即建立映射，打破环的循环依赖
            clone = Node(n.val)
            visited[n.val] = clone

            # 递归复制邻居
            for neighbor in n.neighbors:
                clone.neighbors.append(dfs(neighbor))

            return clone

        return dfs(node)


def test_clone_graph():
    def build_graph(adj_list: list[list[int]]) -> Optional[Node]:
        if not adj_list:
            return None
        nodes = {i: Node(i) for i in range(1, len(adj_list) + 1)}
        for i, neighbors in enumerate(adj_list, 1):
            for n in neighbors:
                nodes[i].neighbors.append(nodes[n])
        return nodes[1]

    def graph_to_adj_list(node: Optional[Node]) -> list[list[int]]:
        if node is None:
            return []
        result_map: dict[int, list[int]] = {}
        stack = [node]
        visited_vals = set()
        while stack:
            n = stack.pop()
            if n.val in visited_vals:
                continue
            visited_vals.add(n.val)
            neighbors = []
            for nb in n.neighbors:
                neighbors.append(nb.val)
                stack.append(nb)
            result_map[n.val] = sorted(neighbors)
        return [result_map[i] for i in range(1, max(result_map.keys()) + 1)]

    # 测试 1: 基本图
    adj1 = [[2, 4], [1, 3], [2, 4], [1, 3]]
    original1 = build_graph(adj1)
    cloned1 = Solution().cloneGraph(original1)
    assert graph_to_adj_list(cloned1) == adj1, "Test 1 failed"

    # 测试 2: 单节点
    adj2 = [[]]
    original2 = build_graph(adj2)
    cloned2 = Solution().cloneGraph(original2)
    assert graph_to_adj_list(cloned2) == adj2, "Test 2 failed"

    # 测试 3: 空图
    assert Solution().cloneGraph(None) is None, "Test 3 failed"

    print("All tests passed for LC 133 - Clone Graph")


if __name__ == "__main__":
    test_clone_graph()
