//! LeetCode 236. 二叉树的最近公共祖先
//!
//! 给定一个二叉树 root 和树中两个节点 p、q，找到并返回它们的最近公共祖先（LCA）。
//!
//! 对标: LeetCode 236 / docs/13-LeetCode算法面试专题/06-面试专题/02-高频Top100-树与图.md

use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, PartialEq, Eq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

/// 查找二叉树中两个节点的最近公共祖先。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：树中节点数范围 `[2, 10^5]`，`p != q`，且均存在于树中。
/// - **后置条件 (Post)**：返回节点 `r`，使得 `p` 和 `q` 分别在 `r` 的左右子树中
///   （或其一就是 `r`），且 `r` 是满足此条件的深度最大的节点。
///
/// # 核心思路
///
/// 后序遍历递归：对于当前节点 root：
/// - 若 root 为空或 root 等于 p 或 q，直接返回 root。
/// - 递归在左子树和右子树查找。
/// - 若左右均非空，说明 p 和 q 分居两侧，当前 root 即为 LCA。
/// - 若仅一侧非空，返回该侧结果。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 最坏情况遍历整棵树。
/// - **空间复杂度**：O(h) — 递归栈深度，h 为树高。
///
/// # 证明要点
///
/// - 引理：对于任意节点 u，若 p 和 q 都在 u 的子树中，则 LCA(p, q) 也在 u 的子树中。
/// - 后序遍历保证先处理子节点。当处理节点 u 时，已知左右子树中是否包含 p 或 q。
/// - 若左右各含一个，u 必为 LCA（且是最近的，更浅的祖先不会同时包含两者于不同子树）。
/// - 若只在一侧，LCA 必在该侧子树中（由引理）。
pub fn lowest_common_ancestor(
    root: Option<Rc<RefCell<TreeNode>>>,
    p: Option<Rc<RefCell<TreeNode>>>,
    q: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    if root.is_none() || root == p || root == q {
        return root;
    }

    let node = root.as_ref().unwrap().borrow();
    let left = lowest_common_ancestor(node.left.clone(), p.clone(), q.clone());
    let right = lowest_common_ancestor(node.right.clone(), p, q);

    if left.is_some() && right.is_some() {
        root
    } else {
        left.or(right)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_tree() -> (
        Option<Rc<RefCell<TreeNode>>>,
        Option<Rc<RefCell<TreeNode>>>,
        Option<Rc<RefCell<TreeNode>>>,
    ) {
        let n3 = Rc::new(RefCell::new(TreeNode::new(3)));
        let n5 = Rc::new(RefCell::new(TreeNode::new(5)));
        let n1 = Rc::new(RefCell::new(TreeNode::new(1)));
        let n6 = Rc::new(RefCell::new(TreeNode::new(6)));
        let n2 = Rc::new(RefCell::new(TreeNode::new(2)));
        let n0 = Rc::new(RefCell::new(TreeNode::new(0)));
        let n8 = Rc::new(RefCell::new(TreeNode::new(8)));
        let n7 = Rc::new(RefCell::new(TreeNode::new(7)));
        let n4 = Rc::new(RefCell::new(TreeNode::new(4)));

        n3.borrow_mut().left = Some(n5.clone());
        n3.borrow_mut().right = Some(n1.clone());
        n5.borrow_mut().left = Some(n6.clone());
        n5.borrow_mut().right = Some(n2.clone());
        n1.borrow_mut().left = Some(n0.clone());
        n1.borrow_mut().right = Some(n8.clone());
        n2.borrow_mut().left = Some(n7.clone());
        n2.borrow_mut().right = Some(n4.clone());

        (Some(n3), Some(n5), Some(n1))
    }

    #[test]
    fn test_example_1() {
        let (root, p, q) = build_tree();
        let lca = lowest_common_ancestor(root.clone(), p.clone(), q.clone());
        assert_eq!(lca.unwrap().borrow().val, 3);
    }

    #[test]
    fn test_example_2() {
        let (root, p, _) = build_tree();
        let n4 = Some(Rc::new(RefCell::new(TreeNode::new(4))));
        let lca = lowest_common_ancestor(root, p, n4);
        assert_eq!(lca.unwrap().borrow().val, 5);
    }
}
