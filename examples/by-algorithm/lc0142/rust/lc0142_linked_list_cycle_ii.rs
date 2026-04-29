//! LeetCode 142. 环形链表 II
//!
//! 给定一个链表，返回链表开始入环的第一个节点；如果无环，返回 None。
//!
//! 对标: LeetCode 142 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md

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

/// 返回链表环的入口节点（Floyd 判圈算法扩展）。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`head` 为链表头节点，可能为 `None`；链表长度 ∈ [0, 10^4]。
/// - **后置条件 (Post)**：若链表存在环，返回环的入口节点；否则返回 `None`。
///
/// # 循环不变式
///
/// **阶段一（相遇判断）**:
/// 慢指针 `slow` 每次走 1 步，快指针 `fast` 每次走 2 步。
/// 若链表中存在环，则 `slow` 与 `fast` 最终必在环上相遇。
///
/// **阶段二（入口定位）**:
/// 设相遇点为 `M`。令指针 `p1` 从 `head` 出发，指针 `p2` 从 `M` 出发，均每次走 1 步。
/// 则 `p1` 与 `p2` 必在环入口相遇。
///
/// **维护**：
/// - 设环外长度为 `a`，环入口到相遇点距离为 `b`，相遇点回到入口距离为 `c`。
/// - 阶段一结束时：`slow` 走了 `a + b` 步，`fast` 走了 `a + b + k(b + c) = 2(a + b)` 步。
/// - 故 `a + b = k(b + c)`，即 `a = (k-1)(b+c) + c`。
/// - 因此从 `head` 走 `a` 步 = 从 `M` 走 `(k-1)` 整圈 + `c` 步，两者恰在入口相遇。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 阶段一 O(n)，阶段二 O(a) ≤ O(n)。
/// - **空间复杂度**：O(1) — 仅使用若干指针变量。
///
/// # 证明要点
///
/// - 入口定位证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md`
/// - 核心等式：`a = (k-1)(b+c) + c`，保证两指针同步走必在入口相遇。
pub fn detect_cycle(head: Option<Rc<RefCell<ListNode>>>) -> Option<Rc<RefCell<ListNode>>> {
    let head_ref = match &head {
        Some(node) => node.clone(),
        None => return None,
    };

    // 阶段一：判断是否有环并找到相遇点
    let mut slow = head_ref.borrow().next.clone();
    let mut fast = match head_ref.borrow().next {
        Some(ref n) => n.borrow().next.clone(),
        None => return None,
    };

    let meeting_point = loop {
        match (slow, fast) {
            (Some(s_node), Some(f_node)) => {
                if Rc::ptr_eq(&s_node, &f_node) {
                    break s_node;
                }
                slow = s_node.borrow().next.clone();
                fast = match f_node.borrow().next {
                    Some(ref n) => n.borrow().next.clone(),
                    None => return None,
                };
            }
            _ => return None,
        }
    };

    // 阶段二：定位环入口
    let mut ptr1 = head_ref;
    let mut ptr2 = meeting_point;

    loop {
        if Rc::ptr_eq(&ptr1, &ptr2) {
            return Some(ptr1);
        }
        let next1 = ptr1.borrow().next.clone();
        let next2 = ptr2.borrow().next.clone();
        ptr1 = match next1 {
            Some(n) => n,
            None => return None,
        };
        ptr2 = match next2 {
            Some(n) => n,
            None => return None,
        };
    }
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
        let result = detect_cycle(Some(node1));
        assert!(result.is_some());
        assert!(Rc::ptr_eq(&result.unwrap(), &node2));
    }

    #[test]
    fn test_example_2_no_cycle() {
        let node_a = ListNode::new(1);
        let node_b = ListNode::new(2);
        node_a.borrow_mut().next = Some(node_b.clone());
        assert!(detect_cycle(Some(node_a)).is_none());
    }

    #[test]
    fn test_empty_list() {
        assert!(detect_cycle(None).is_none());
    }

    #[test]
    fn test_single_node_no_cycle() {
        let single = ListNode::new(1);
        assert!(detect_cycle(Some(single)).is_none());
    }

    #[test]
    fn test_self_loop() {
        let self_loop = ListNode::new(1);
        self_loop.borrow_mut().next = Some(self_loop.clone());
        let result = detect_cycle(Some(self_loop.clone()));
        assert!(result.is_some());
        assert!(Rc::ptr_eq(&result.unwrap(), &self_loop));
    }

    #[test]
    fn test_two_node_cycle() {
        let n1 = ListNode::new(1);
        let n2 = ListNode::new(2);
        n1.borrow_mut().next = Some(n2.clone());
        n2.borrow_mut().next = Some(n1.clone());
        let result = detect_cycle(Some(n1.clone()));
        assert!(result.is_some());
        assert!(Rc::ptr_eq(&result.unwrap(), &n1));
    }
}
