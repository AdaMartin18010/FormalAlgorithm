//! LeetCode 206. 反转链表
//!
//! 给你单链表的头节点 head，请你反转链表，并返回反转后的链表。
//!
//! 对标: LeetCode 206 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

// Definition for singly-linked list.
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    pub fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }
}

/// 反转单链表。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：链表长度范围 `[0, 5 * 10^4]`。
/// - **后置条件 (Post)**：返回原链表的反转链表头节点。
///
/// # 核心思路
///
/// 迭代法：维护 `prev`（已反转部分的头）和 `curr`（待反转的当前节点）。
/// 每次将 `curr.next` 指向 `prev`，然后两者各前进一步。
///
/// # 循环不变式
///
/// 1. 从 `prev` 出发沿 `next` 遍历得到原链表 `[0..curr_prev]` 的逆序。
/// 2. 从 `curr` 出发沿 `next` 遍历得到原链表 `[curr..end]` 的正序。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — 遍历链表一次。
/// - **空间复杂度**：O(1) — 仅使用常数个额外指针。
///
/// # 证明要点
///
/// - 初始化：`prev = None`, `curr = head`，已反转部分为空，不变式成立。
/// - 保持：设 `next_node = curr.next`，`curr.next = prev` 后，`curr` 成为新的已反转部分的头，不变式保持。
/// - 终止：`curr = None` 时，已反转部分包含全部节点，返回 `prev`。
pub fn reverse_list(head: Option<Box<ListNode>>) -> Option<Box<ListNode>> {
    let mut prev: Option<Box<ListNode>> = None;
    let mut curr = head;

    while let Some(mut curr_node) = curr {
        let next_node = curr_node.next.take();
        curr_node.next = prev;
        prev = Some(curr_node);
        curr = next_node;
    }

    prev
}

#[cfg(test)]
mod tests {
    use super::*;

    fn vec_to_list(vals: Vec<i32>) -> Option<Box<ListNode>> {
        let mut head: Option<Box<ListNode>> = None;
        for &v in vals.iter().rev() {
            let mut node = Box::new(ListNode::new(v));
            node.next = head;
            head = Some(node);
        }
        head
    }

    fn list_to_vec(head: Option<Box<ListNode>>) -> Vec<i32> {
        let mut result = Vec::new();
        let mut curr = head;
        while let Some(node) = curr {
            result.push(node.val);
            curr = node.next;
        }
        result
    }

    #[test]
    fn test_example_1() {
        let head = vec_to_list(vec![1, 2, 3, 4, 5]);
        assert_eq!(list_to_vec(reverse_list(head)), vec![5, 4, 3, 2, 1]);
    }

    #[test]
    fn test_example_2() {
        let head = vec_to_list(vec![1, 2]);
        assert_eq!(list_to_vec(reverse_list(head)), vec![2, 1]);
    }

    #[test]
    fn test_empty() {
        assert_eq!(list_to_vec(reverse_list(None)), Vec::<i32>::new());
    }

    #[test]
    fn test_single() {
        let head = vec_to_list(vec![1]);
        assert_eq!(list_to_vec(reverse_list(head)), vec![1]);
    }
}
