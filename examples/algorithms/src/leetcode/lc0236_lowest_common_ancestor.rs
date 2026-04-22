/// LeetCode 236 - Lowest Common Ancestor of a Binary Tree
/// https://leetcode.com/problems/lowest-common-ancestor-of-a-binary-tree/
///
/// 题目：给定二叉树根节点 root 和两个节点 p, q，找到它们的最近公共祖先。
///
/// 思路：递归后序遍历。
///       - 若当前节点为 null 或等于 p 或 q，返回当前节点
///       - 递归查找左子树和右子树
///       - 若左右子树均找到，当前节点即为 LCA
///       - 若仅一侧找到，返回该侧结果
/// 时间复杂度：O(n)
/// 空间复杂度：O(h)

use std::cell::RefCell;
use std::rc::Rc;

#[derive(Debug, Clone, PartialEq)]
pub struct TreeNode {
    pub val: i32,
    pub left: Option<Rc<RefCell<TreeNode>>>,
    pub right: Option<Rc<RefCell<TreeNode>>>,
}

impl TreeNode {
    pub fn new(val: i32) -> Self {
        TreeNode {
            val,
            left: None,
            right: None,
        }
    }
}

pub fn lowest_common_ancestor(
    root: Option<Rc<RefCell<TreeNode>>>,
    p: Option<Rc<RefCell<TreeNode>>>,
    q: Option<Rc<RefCell<TreeNode>>>,
) -> Option<Rc<RefCell<TreeNode>>> {
    if root.is_none() {
        return None;
    }
    let r = root.clone().unwrap();
    let rv = r.borrow();
    if Some(r.clone()) == p || Some(r.clone()) == q {
        return Some(r.clone());
    }
    drop(rv);
    let left = lowest_common_ancestor(r.borrow().left.clone(), p.clone(), q.clone());
    let right = lowest_common_ancestor(r.borrow().right.clone(), p.clone(), q.clone());
    if left.is_some() && right.is_some() {
        return Some(r.clone());
    }
    left.or(right)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lca_normal() {
        // 树结构：
        //        3
        //       / \
        //      5   1
        //     / \ / \
        //    6  2 0  8
        //      / \
        //     7   4
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

        // p=5, q=1 -> LCA = 3
        let lca = lowest_common_ancestor(Some(n3.clone()), Some(n5.clone()), Some(n1.clone()));
        assert!(lca.is_some());
        assert_eq!(lca.unwrap().borrow().val, 3);

        // p=5, q=4 -> LCA = 5
        let lca2 = lowest_common_ancestor(Some(n3.clone()), Some(n5.clone()), Some(n4.clone()));
        assert!(lca2.is_some());
        assert_eq!(lca2.unwrap().borrow().val, 5);
    }

    #[test]
    fn test_lca_single_child() {
        let n1 = Rc::new(RefCell::new(TreeNode::new(1)));
        let n2 = Rc::new(RefCell::new(TreeNode::new(2)));
        n1.borrow_mut().left = Some(n2.clone());

        let lca = lowest_common_ancestor(Some(n1.clone()), Some(n1.clone()), Some(n2.clone()));
        assert!(lca.is_some());
        assert_eq!(lca.unwrap().borrow().val, 1);
    }
}
