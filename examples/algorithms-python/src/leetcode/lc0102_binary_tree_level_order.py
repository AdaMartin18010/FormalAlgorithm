"""
LeetCode 102. Binary Tree Level Order Traversal
链接: https://leetcode.com/problems/binary-tree-level-order-traversal/
难度: Medium

题目描述:
给你二叉树的根节点 root，返回其节点值的层序遍历。（即逐层地，从左到右访问所有节点）。

形式化规约:
  输入: 二叉树根节点 root
  输出: 按层遍历的节点值列表，每层一个子列表

最优解思路:
  BFS：用队列维护当前层的所有节点。每次处理一层时，先记录当前队列大小 size，
  然后恰好弹出 size 个节点（即为当前层所有节点），将它们的子节点入队。

复杂度:
  时间: O(n)
  空间: O(w)，w 为最大层宽，最坏 O(n)

正确性要点:
  1. 通过记录队列大小来区分不同层，避免额外标记
  2. 这是 BFS 在树结构上的经典应用
"""

from typing import Optional, List
from collections import deque


class TreeNode:
    def __init__(self, val: int = 0,
                 left: Optional['TreeNode'] = None,
                 right: Optional['TreeNode'] = None):
        self.val = val
        self.left = left
        self.right = right


class Solution:
    def levelOrder(self, root: Optional[TreeNode]) -> List[List[int]]:
        """
        BFS 层序遍历。时间 O(n)，空间 O(w)。
        """
        if not root:
            return []

        result = []
        queue = deque([root])

        while queue:
            level_size = len(queue)
            level_vals = []
            for _ in range(level_size):
                node = queue.popleft()
                level_vals.append(node.val)
                if node.left:
                    queue.append(node.left)
                if node.right:
                    queue.append(node.right)
            result.append(level_vals)

        return result


def build_tree(vals: list[Optional[int]], index: int = 0) -> Optional[TreeNode]:
    """按层序列表构建二叉树，None 表示空节点。"""
    if index >= len(vals) or vals[index] is None:
        return None
    root = TreeNode(vals[index])  # type: ignore[arg-type]
    root.left = build_tree(vals, 2 * index + 1)
    root.right = build_tree(vals, 2 * index + 2)
    return root


def test_level_order():
    sol = Solution()
    # 示例 1
    root1 = build_tree([3, 9, 20, None, None, 15, 7])
    res1 = sol.levelOrder(root1)
    assert res1 == [[3], [9, 20], [15, 7]], f"Test 1 failed: {res1}"
    # 示例 2: 空树
    assert sol.levelOrder(None) == [], "Test 2 failed"
    # 示例 3: 单节点
    root3 = build_tree([1])
    assert sol.levelOrder(root3) == [[1]], "Test 3 failed"
    print("All tests passed for LC 102 - Binary Tree Level Order Traversal")


if __name__ == "__main__":
    test_level_order()
