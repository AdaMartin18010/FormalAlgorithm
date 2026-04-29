"""
LeetCode 226. Invert Binary Tree
链接: https://leetcode.com/problems/invert-binary-tree/
难度: Easy

题目描述:
翻转一棵二叉树（镜像）。

形式化规约:
  输入: 二叉树根节点 root
  输出: 翻转后的二叉树根节点

最优解思路:
  递归后序遍历。先递归翻转左右子树，再交换当前节点的左右子节点。

复杂度:
  时间: O(n)
  空间: O(h)，h 为树高

正确性要点:
  1. 空树直接返回
  2. 先递归处理子树，确保子树已经翻转
  3. 交换左右指针完成当前节点的翻转
"""

from typing import Optional


class TreeNode:
    """二叉树节点定义。"""

    def __init__(
        self,
        val: int = 0,
        left: Optional["TreeNode"] = None,
        right: Optional["TreeNode"] = None,
    ):
        self.val = val
        self.left = left
        self.right = right


def invert_tree(root: Optional[TreeNode]) -> Optional[TreeNode]:
    """
    递归翻转二叉树。
    时间复杂度 O(n)，空间复杂度 O(h)。
    """
    if root is None:
        return None

    # 递归翻转左右子树
    left = invert_tree(root.left)
    right = invert_tree(root.right)

    # 交换左右子节点
    root.left = right
    root.right = left

    return root


def inorder_traversal(root: Optional[TreeNode]) -> list[int]:
    """中序遍历辅助函数，用于验证结果。"""
    result = []
    if root:
        result.extend(inorder_traversal(root.left))
        result.append(root.val)
        result.extend(inorder_traversal(root.right))
    return result


if __name__ == "__main__":
    # 示例 1:
    #      4
    #     / \
    #    2   7
    #   / \ / \
    #  1  3 6  9
    root = TreeNode(
        4,
        TreeNode(2, TreeNode(1), TreeNode(3)),
        TreeNode(7, TreeNode(6), TreeNode(9)),
    )
    inverted = invert_tree(root)
    assert inorder_traversal(inverted) == [9, 7, 6, 4, 3, 2, 1], "Example 1 failed"

    # 边界: 空树
    assert invert_tree(None) is None, "Empty tree failed"

    # 边界: 单节点
    single = TreeNode(1)
    assert inorder_traversal(invert_tree(single)) == [1], "Single node failed"

    print("All tests passed for LC 226 - Invert Binary Tree")
