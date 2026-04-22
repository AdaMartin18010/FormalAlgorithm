"""LeetCode 102. 二叉树的层序遍历 — Python 实现

给定一个二叉树，返回其节点值的层序遍历（即逐层从左到右）。

对标: LeetCode 102 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md
"""

from typing import List, Optional
from collections import deque


class TreeNode:
    """二叉树节点定义。"""

    def __init__(self, val: int = 0, left: Optional["TreeNode"] = None, right: Optional["TreeNode"] = None):
        self.val = val
        self.left = left
        self.right = right


def level_order(root: Optional[TreeNode]) -> List[List[int]]:
    """返回二叉树的层序遍历结果。

    前置条件 (Pre):
        - root 为二叉树根节点，或为 None。
        - 节点值范围为 [-1000, 1000]。

    后置条件 (Post):
        - 返回二维列表，第 i 个列表包含第 i 层所有节点值（从左到右）。

    BFS 层级不变式 (Layer Invariant):
        处理第 d 层前，队列中恰好包含第 d 层所有节点（从左到右顺序）。
        处理完成后，队列中恰好包含第 d+1 层所有节点。

    复杂度:
        时间复杂度: O(n) — n 为节点总数，每个节点访问一次。
        空间复杂度: O(w) — w 为树的最大宽度，即队列最大长度。

    证明要点:
        - 初始化：队列放入根节点，满足第 0 层不变式。
        - 保持：处理当前层时，将每个节点的左右子节点依次入队，保证下一层节点顺序正确。
        - 终止：队列为空时，所有层均已处理完毕。

    Args:
        root: 二叉树根节点。

    Returns:
        层序遍历结果。
    """
    if root is None:
        return []

    result: List[List[int]] = []
    queue = deque([root])

    while queue:
        level_size = len(queue)
        level = []
        for _ in range(level_size):
            node = queue.popleft()
            level.append(node.val)
            if node.left:
                queue.append(node.left)
            if node.right:
                queue.append(node.right)
        result.append(level)

    return result


if __name__ == "__main__":
    # LeetCode 官方示例
    # [3, 9, 20, null, null, 15, 7]
    root = TreeNode(3)
    root.left = TreeNode(9)
    root.right = TreeNode(20)
    root.right.left = TreeNode(15)
    root.right.right = TreeNode(7)
    assert level_order(root) == [[3], [9, 20], [15, 7]], "Example 1 failed"

    # 边界条件
    assert level_order(None) == [], "Empty tree"
    single = TreeNode(1)
    assert level_order(single) == [[1]], "Single node"

    # 只有左子树
    left_only = TreeNode(1, TreeNode(2, TreeNode(3)))
    assert level_order(left_only) == [[1], [2], [3]], "Left only tree"

    print("All tests passed.")
