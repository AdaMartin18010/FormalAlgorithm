"""
LeetCode 94. Binary Tree Inorder Traversal
链接: https://leetcode.com/problems/binary-tree-inorder-traversal/
难度: Easy

题目描述:
给定二叉树的根节点 root，返回其节点值的中序遍历（左-根-右）。

形式化规约:
  输入: 二叉树根节点 root
  输出: 中序遍历序列 [左子树, 根, 右子树]

最优解思路:
  1. 递归 DFS：先递归遍历左子树，再访问根节点，最后递归遍历右子树。
  2. 迭代法：使用栈模拟递归过程，先一路向左入栈，然后弹出访问，再转向右子树。

复杂度:
  时间: O(n)，每个节点访问一次
  空间: O(h)，h 为树高（递归栈或显式栈）

正确性要点:
  1. 中序遍历顺序严格为左-根-右
  2. 迭代法中栈保存待访问的节点路径
  3. 访问完左子树后访问根，再处理右子树
"""

from typing import List, Optional


class TreeNode:
    def __init__(self, val: int = 0,
                 left: Optional['TreeNode'] = None,
                 right: Optional['TreeNode'] = None):
        self.val = val
        self.left = left
        self.right = right


class Solution:
    def inorderTraversal(self, root: Optional[TreeNode]) -> List[int]:
        """
        递归中序遍历。
        """
        result: List[int] = []

        def dfs(node: Optional[TreeNode]):
            if not node:
                return
            dfs(node.left)
            result.append(node.val)
            dfs(node.right)

        dfs(root)
        return result

    def inorderTraversalIterative(self, root: Optional[TreeNode]) -> List[int]:
        """
        迭代中序遍历（栈模拟）。
        """
        result: List[int] = []
        stack: List[TreeNode] = []
        current = root

        while current or stack:
            while current:
                stack.append(current)
                current = current.left
            current = stack.pop()
            result.append(current.val)
            current = current.right

        return result


def test_inorder_traversal():
    sol = Solution()
    # 树结构：
    #      1
    #       \
    #        2
    #       /
    #      3
    root = TreeNode(1, None, TreeNode(2, TreeNode(3), None))
    assert sol.inorderTraversal(root) == [1, 3, 2]
    assert sol.inorderTraversalIterative(root) == [1, 3, 2]

    # 空树
    assert sol.inorderTraversal(None) == []
    assert sol.inorderTraversalIterative(None) == []

    # 单节点
    single = TreeNode(42)
    assert sol.inorderTraversal(single) == [42]
    assert sol.inorderTraversalIterative(single) == [42]

    # 完全二叉树：
    #      4
    #     / \
    #    2   6
    #   / \ / \
    #  1  3 5  7
    complete = TreeNode(
        4,
        TreeNode(2, TreeNode(1), TreeNode(3)),
        TreeNode(6, TreeNode(5), TreeNode(7)),
    )
    assert sol.inorderTraversal(complete) == [1, 2, 3, 4, 5, 6, 7]
    assert sol.inorderTraversalIterative(complete) == [1, 2, 3, 4, 5, 6, 7]

    print("All tests passed for LC 94 - Binary Tree Inorder Traversal")


if __name__ == "__main__":
    test_inorder_traversal()
