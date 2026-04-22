"""LeetCode 236. 二叉树的最近公共祖先 — Python 实现

给定一个二叉树 root 和树中两个节点 p、q，找到并返回它们的最近公共祖先（LCA）。

对标: LeetCode 236 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md
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


def lowest_common_ancestor(
    root: TreeNode, p: TreeNode, q: TreeNode
) -> TreeNode:
    """查找二叉树中两个节点的最近公共祖先。

    前置条件 (Pre):
        - root 为非空二叉树根节点，节点数范围 [2, 10^5]。
        - p != q，且 p 和 q 均存在于树中。

    后置条件 (Post):
        - 返回节点 r，使得 p 和 q 分别在 r 的左右子树中（或其一就是 r），
          且 r 是满足此条件的深度最大的节点。

    核心思路:
        后序遍历递归：对于当前节点 root：
        - 若 root 为空或 root 等于 p 或 q，直接返回 root。
        - 递归在左子树查找 LCA，在右子树查找 LCA。
        - 若左右子树均非空返回，说明 p 和 q 分居两侧，当前 root 即为 LCA。
        - 若仅一侧非空，说明 p 和 q 都在该侧，返回该侧结果。

    复杂度:
        时间复杂度: O(n) — 最坏情况遍历整棵树。
        空间复杂度: O(h) — 递归栈深度，h 为树高。

    证明要点:
        - 引理：对于任意节点 u，若 p 和 q 都在 u 的子树中，则 LCA(p, q)
          也在 u 的子树中。
        - 后序遍历保证先处理子节点再处理父节点。当处理节点 u 时，
          已知左子树和右子树中是否包含 p 或 q。
        - 若左右各含一个，u 必为 LCA（且是最近的，因为更浅的祖先不会
          同时包含两者于不同子树）。
        - 若只在一侧，LCA 必在该侧子树中（由引理）。

    Args:
        root: 二叉树根节点。
        p: 树中节点之一。
        q: 树中另一节点。

    Returns:
        p 和 q 的最近公共祖先节点。
    """
    if root is None or root == p or root == q:
        return root

    left = lowest_common_ancestor(root.left, p, q)  # type: ignore[arg-type]
    right = lowest_common_ancestor(root.right, p, q)  # type: ignore[arg-type]

    if left and right:
        return root
    return left if left else right


if __name__ == "__main__":
    # 构建测试树: root = [3,5,1,6,2,0,8,null,null,7,4]
    root = TreeNode(3)
    n5 = TreeNode(5)
    n1 = TreeNode(1)
    n6 = TreeNode(6)
    n2 = TreeNode(2)
    n0 = TreeNode(0)
    n8 = TreeNode(8)
    n7 = TreeNode(7)
    n4 = TreeNode(4)

    root.left = n5
    root.right = n1
    n5.left = n6
    n5.right = n2
    n1.left = n0
    n1.right = n8
    n2.left = n7
    n2.right = n4

    assert lowest_common_ancestor(root, n5, n1) == root, "Example 1 failed"
    assert lowest_common_ancestor(root, n5, n4) == n5, "Example 2 failed"

    # 简单树
    simple = TreeNode(1, TreeNode(2), TreeNode(3))
    n2s = simple.left
    n3s = simple.right
    assert lowest_common_ancestor(simple, n2s, n3s) == simple, "Simple tree"

    # 链状树
    chain = TreeNode(1, TreeNode(2, TreeNode(3)))
    n2c = chain.left
    n3c = chain.left.left  # type: ignore[union-attr]
    assert lowest_common_ancestor(chain, n2c, n3c) == n2c, "Chain tree"

    print("All tests passed.")
