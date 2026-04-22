//! LeetCode 23. 合并 K 个升序链表（分治版本）
//!
//! 分治合并策略：将 k 个链表两两配对合并，每轮链表数量减半。
//!
//! 对标: LeetCode 23 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md

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

/// 分治合并 k 个升序链表。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`lists` 包含 `k` 个已升序链表。
/// - **后置条件 (Post)**：返回一个升序链表，包含所有输入链表中的全部节点。
///
/// # 核心思路
///
/// 分治合并：
/// - Round 1: k 个链表 → k/2 个链表（两两合并）
/// - Round 2: k/2 个链表 → k/4 个链表
/// - ...
/// - Round log k: 1 个有序链表
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(N log k)` — `N` 为总节点数，共 `log k` 轮合并。
/// - **空间复杂度**：`O(log k)` — 递归栈深度。
pub fn merge_k_lists(lists: Vec<Option<Box<ListNode>>>) -> Option<Box<ListNode>> {
    let n = lists.len();
    if n == 0 {
        return None;
    }
    merge_range(&lists, 0, n - 1)
}

fn merge_range(lists: &[Option<Box<ListNode>>], left: usize, right: usize) -> Option<Box<ListNode>> {
    if left == right {
        return lists[left].clone();
    }
    let mid = left + (right - left) / 2;
    let l1 = merge_range(lists, left, mid);
    let l2 = merge_range(lists, mid + 1, right);
    merge_two(l1, l2)
}

fn merge_two(
    mut l1: Option<Box<ListNode>>,
    mut l2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    let mut dummy = Box::new(ListNode::new(0));
    let mut tail = &mut dummy as *mut Box<ListNode>;

    while l1.is_some() && l2.is_some() {
        let v1 = l1.as_ref().unwrap().val;
        let v2 = l2.as_ref().unwrap().val;
        if v1 <= v2 {
            let next = l1.as_mut().unwrap().next.take();
            unsafe {
                (*tail).next = l1;
                tail = (*tail).next.as_mut().unwrap() as *mut Box<ListNode>;
            }
            l1 = next;
        } else {
            let next = l2.as_mut().unwrap().next.take();
            unsafe {
                (*tail).next = l2;
                tail = (*tail).next.as_mut().unwrap() as *mut Box<ListNode>;
            }
            l2 = next;
        }
    }

    unsafe {
        (*tail).next = if l1.is_some() { l1 } else { l2 };
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
}
