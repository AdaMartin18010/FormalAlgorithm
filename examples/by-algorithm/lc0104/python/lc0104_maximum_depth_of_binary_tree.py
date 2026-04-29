"""LeetCode 104. 二叉树的最大深度 — Python 实现

给定一个二叉树 root，返回其最大深度。
二叉树的最大深度是指从根节点到最远叶子节点的最长路径上的节点数。

对标: LeetCode 104 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md
"""

from typing import Optional
from collections import deque


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


def max_depth(root: Optional[TreeNode]) -> int:
    """计算二叉树的最大深度。

    前置条件 (Pre):
        - root 为二叉树根节点，树中节点总数范围 [0, 10^4]。
        - 节点值范围 [-100, 100]。

    后置条件 (Post):
        - 返回从根节点到最远叶子节点的路径上的节点数。

    核心思路:
        递归法（DFS）：树的最大深度 = 1 + max(左子树深度, 右子树深度)。
        空树深度为 0。

    复杂度:
        时间复杂度: O(n) — 访问每个节点一次。
        空间复杂度: O(h) — 递归栈深度，h 为树高；最坏情况 O(n)，平均 O(log n)。

    证明要点:
        - 归纳基础：空树深度为 0，叶子节点深度为 1，正确。
        - 归纳步骤：假设左子树和右子树的 max_depth 分别正确返回 dl, dr。
          则当前树的最大深度为 1 + max(dl, dr)，因为从根到最深叶子必须
          经过左子树或右子树中最深的路径，加上根节点本身。

    Args:
        root: 二叉树根节点。

    Returns:
        二叉树的最大深度。
    """
    if root is None:
        return 0
    return 1 + max(max_depth(root.left), max_depth(root.right))


def max_depth_iterative(root: Optional[TreeNode]) -> int:
    """迭代法（BFS 层序遍历）计算二叉树最大深度。

    复杂度:
        时间复杂度: O(n)
        空间复杂度: O(w)，w 为树的最大宽度。

    证明要点:
        BFS 按层遍历，每层深度加 1，遍历完所有层后得到的深度即为最大深度。
    """
    if root is None:
        return 0
    queue = deque([root])
    depth = 0
    while queue:
        depth += 1
        for _ in range(len(queue)):
            node = queue.popleft()
            if node.left:
                queue.append(node.left)
            if node.right:
                queue.append(node.right)
    return depth


if __name__ == "__main__":
    # LeetCode 官方示例
    root1 = TreeNode(3, TreeNode(9), TreeNode(20, TreeNode(15), TreeNode(7)))
    assert max_depth(root1) == 3, "Example 1 failed"
    assert max_depth_iterative(root1) == 3, "Example 1 iterative failed"

    root2 = TreeNode(1, None, TreeNode(2))
    assert max_depth(root2) == 2, "Example 2 failed"

    # 边界条件
    assert max_depth(None) == 0, "Empty tree"
    assert max_depth(TreeNode(0)) == 1, "Single node"

    # 链状树
    chain = TreeNode(1, TreeNode(2, TreeNode(3, TreeNode(4))))
    assert max_depth(chain) == 4, "Chain tree"

    print("All tests passed.")
