//! LeetCode 141. 环形链表
//!
//! 给定一个链表，判断链表中是否有环。
//!
//! 对标: LeetCode 141 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md

use std::cell::RefCell;
use std::rc::Rc;

/// 链表节点定义（使用 Rc<RefCell> 以支持环结构）。
pub struct ListNode {
    pub val: i32,
    pub next: Option<Rc<RefCell<ListNode>>>,
}

impl ListNode {
    /// 创建一个新节点并包装为 Rc<RefCell>。
    pub fn new(val: i32) -> Rc<RefCell<ListNode>> {
        Rc::new(RefCell::new(ListNode { val, next: None }))
    }
}

/// 判断链表中是否存在环（Floyd 判圈算法）。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`head` 为链表头节点，可能为 `None`；链表长度 ∈ [0, 10^4]。
/// - **后置条件 (Post)**：若链表存在环返回 `true`，否则返回 `false`。
///
/// # 循环不变式
///
/// 设慢指针 `slow` 每次走 1 步，快指针 `fast` 每次走 2 步。
/// 若链表中存在环，则 `slow` 与 `fast` 最终必在环上相遇。
///
/// **维护**：
/// - 初始 `slow = head`, `fast = head.next`（或 `head`）。
/// - 每轮迭代：`slow = slow.next`, `fast = fast.next.next`。
/// - 若 `fast` 或 `fast.next` 为 `None`，说明无环，返回 `false`。
/// - 若 `slow == fast`，说明相遇，返回 `true`。
///
/// **终止推出**：无环时 `fast` 走到末尾；有环时 `slow == fast`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 无环时 `fast` 遍历最多 n 个节点；
///   有环时，设环外长度为 a，环长为 c，则 `slow` 进入环后最多再走 c 步即与 `fast` 相遇。
/// - **空间复杂度**：O(1) — 仅使用两个指针变量。
///
/// # 证明要点
///
/// - 相遇定理证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md`
/// - 关键引理：有环时，`fast` 相对 `slow` 的速度为 1 步/轮，必能追上。
pub fn has_cycle(head: Option<Rc<RefCell<ListNode>>>) -> bool {
    let slow_ptr = match &head {
        Some(node) => node.borrow().next.clone(),
        None => return false,
    };

    let mut slow = slow_ptr;
    let mut fast = match &head {
        Some(node) => match &node.borrow().next {
            Some(n) => n.borrow().next.clone(),
            None => return false,
        },
        None => return false,
    };

    while let (Some(s_node), Some(f_node)) = (slow, fast) {
        if Rc::ptr_eq(&s_node, &f_node) {
            return true;
        }
        slow = s_node.borrow().next.clone();
        fast = match &f_node.borrow().next {
            Some(n) => n.borrow().next.clone(),
            None => return false,
        };
    }

    false
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1_cycle() {
        let node1 = ListNode::new(3);
        let node2 = ListNode::new(2);
        let node3 = ListNode::new(0);
        let node4 = ListNode::new(-4);
        node1.borrow_mut().next = Some(node2.clone());
        node2.borrow_mut().next = Some(node3.clone());
        node3.borrow_mut().next = Some(node4.clone());
        node4.borrow_mut().next = Some(node2.clone());
        assert!(has_cycle(Some(node1)));
    }

    #[test]
    fn test_example_2_no_cycle() {
        let node_a = ListNode::new(1);
        let node_b = ListNode::new(2);
        node_a.borrow_mut().next = Some(node_b.clone());
        assert!(!has_cycle(Some(node_a)));
    }

    #[test]
    fn test_empty_list() {
        assert!(!has_cycle(None));
    }

    #[test]
    fn test_single_node_no_cycle() {
        let single = ListNode::new(1);
        assert!(!has_cycle(Some(single)));
    }

    #[test]
    fn test_self_loop() {
        let self_loop = ListNode::new(1);
        self_loop.borrow_mut().next = Some(self_loop.clone());
        assert!(has_cycle(Some(self_loop)));
    }

    #[test]
    fn test_two_node_cycle() {
        let n1 = ListNode::new(1);
        let n2 = ListNode::new(2);
        n1.borrow_mut().next = Some(n2.clone());
        n2.borrow_mut().next = Some(n1.clone());
        assert!(has_cycle(Some(n1)));
    }
}
