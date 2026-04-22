//! LeetCode 23. 合并 K 个升序链表
//!
//! 给你一个链表数组，每个链表都已经按升序排列。
//! 请你将所有链表合并到一个升序链表中，返回合并后的链表。
//!
//! 对标: LeetCode 23 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md

use std::cmp::Ordering;
use std::collections::BinaryHeap;

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

// 为 ListNode 实现 Ord 以支持 BinaryHeap
// 注意：需要反转比较顺序以获得最小堆
#[derive(Eq, PartialEq)]
struct HeapNode(Box<ListNode>);

impl Ord for HeapNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.val.cmp(&self.0.val)
    }
}

impl PartialOrd for HeapNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

/// 合并 K 个升序链表。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`lists` 包含 `k` 个已升序链表，`k` 范围 `[0, 10^4]`，总节点数不超过 `10^5`。
/// - **后置条件 (Post)**：返回一个升序链表，包含所有输入链表中的全部节点。
///
/// # 核心思路
///
/// 最小堆法：维护一个大小为 k 的最小堆，存储每个链表的当前头节点。
/// 每次从堆顶取出最小元素加入结果链表，并将该元素所在链表的下一个节点入堆。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(N log k) — N 为总节点数，每次堆操作 O(log k)。
/// - **空间复杂度**：O(k) — 堆中最多同时存在 k 个元素。
///
/// # 证明要点
///
/// - 不变式：堆中始终包含每个非空输入链表的当前最小未处理节点。
/// - 每次取出的节点 val 不大于堆中任何其他节点，因此按取出顺序链接得到的链表是全局升序的。
/// - 终止时所有节点均被取出并链接，结果链表包含全部 N 个节点。
pub fn merge_k_lists(lists: Vec<Option<Box<ListNode>>>) -> Option<Box<ListNode>> {
    let mut heap: BinaryHeap<HeapNode> = BinaryHeap::new();

    for node in lists {
        if let Some(n) = node {
            heap.push(HeapNode(n));
        }
    }

    let mut dummy = Box::new(ListNode::new(0));
    let mut tail = &mut dummy as *mut Box<ListNode>;

    while let Some(HeapNode(mut node)) = heap.pop() {
        if let Some(next) = node.next.take() {
            heap.push(HeapNode(next));
        }
        unsafe {
            (*tail).next = Some(node);
            tail = (*tail).next.as_mut().unwrap() as *mut Box<ListNode>;
        }
    }

    dummy.next
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
        let lists = vec![
            vec_to_list(vec![1, 4, 5]),
            vec_to_list(vec![1, 3, 4]),
            vec_to_list(vec![2, 6]),
        ];
        assert_eq!(
            list_to_vec(merge_k_lists(lists)),
            vec![1, 1, 2, 3, 4, 4, 5, 6]
        );
    }

    #[test]
    fn test_empty_lists() {
        let lists: Vec<Option<Box<ListNode>>> = vec![];
        assert_eq!(list_to_vec(merge_k_lists(lists)), Vec::<i32>::new());
    }

    #[test]
    fn test_all_null() {
        let lists: Vec<Option<Box<ListNode>>> = vec![None, None];
        assert_eq!(list_to_vec(merge_k_lists(lists)), Vec::<i32>::new());
    }

    #[test]
    fn test_two_single() {
        let lists = vec![vec_to_list(vec![1]), vec_to_list(vec![0])];
        assert_eq!(list_to_vec(merge_k_lists(lists)), vec![0, 1]);
    }
}
