/// LeetCode 21. Merge Two Sorted Lists
/// https://leetcode.com/problems/merge-two-sorted-lists/
///
/// Problem: Merge two sorted linked lists and return it as a new sorted list.
/// The new list should be made by splicing together the nodes of the first two lists.
///
/// Formal specification:
/// - Pre: l1 and l2 are sorted in non-decreasing order
/// - Post: result is sorted and contains exactly the multiset union of l1 and l2
///
/// Algorithm: Recursive merge with O(n+m) time, O(n+m) space (call stack).
///
/// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/06-双指针.md
/// Lean proof: examples/lean_proofs/leetcode/lc0021_merge_two_sorted_lists.lean

// Definition for singly-linked list provided by LeetCode
#[derive(PartialEq, Eq, Clone, Debug)]
pub struct ListNode {
    pub val: i32,
    pub next: Option<Box<ListNode>>,
}

impl ListNode {
    #[inline]
    fn new(val: i32) -> Self {
        ListNode { next: None, val }
    }
}

pub fn merge_two_lists(
    list1: Option<Box<ListNode>>,
    list2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    match (list1, list2) {
        (None, None) => None,
        (Some(l), None) => Some(l),
        (None, Some(r)) => Some(r),
        (Some(mut l), Some(mut r)) => {
            if l.val <= r.val {
                l.next = merge_two_lists(l.next, Some(r));
                Some(l)
            } else {
                r.next = merge_two_lists(Some(l), r.next);
                Some(r)
            }
        }
    }
}

// Iterative version with O(1) extra space
pub fn merge_two_lists_iterative(
    list1: Option<Box<ListNode>>,
    list2: Option<Box<ListNode>>,
) -> Option<Box<ListNode>> {
    let mut dummy = Box::new(ListNode::new(0));
    let mut tail = &mut dummy.next;
    let (mut l1, mut l2) = (list1, list2);

    while let (Some(ref n1), Some(ref n2)) = (&l1, &l2) {
        if n1.val <= n2.val {
            let next = l1.as_mut().unwrap().next.take();
            *tail = l1;
            l1 = next;
        } else {
            let next = l2.as_mut().unwrap().next.take();
            *tail = l2;
            l2 = next;
        }
        tail = &mut tail.as_mut().unwrap().next;
    }

    *tail = if l1.is_some() { l1 } else { l2 };
    dummy.next
}

#[cfg(test)]
mod tests {
    use super::*;

    fn build_list(vals: Vec<i32>) -> Option<Box<ListNode>> {
        let mut head = None;
        for &val in vals.iter().rev() {
            let mut node = Box::new(ListNode::new(val));
            node.next = head;
            head = Some(node);
        }
        head
    }

    fn list_to_vec(head: Option<Box<ListNode>>) -> Vec<i32> {
        let mut res = vec![];
        let mut curr = head;
        while let Some(node) = curr {
            res.push(node.val);
            curr = node.next;
        }
        res
    }

    #[test]
    fn test_example_1() {
        let l1 = build_list(vec![1, 2, 4]);
        let l2 = build_list(vec![1, 3, 4]);
        let merged = merge_two_lists(l1, l2);
        assert_eq!(list_to_vec(merged), vec![1, 1, 2, 3, 4, 4]);
    }

    #[test]
    fn test_empty_lists() {
        assert_eq!(list_to_vec(merge_two_lists(None, None)), Vec::<i32>::new());
        let l = build_list(vec![0]);
        assert_eq!(list_to_vec(merge_two_lists(l.clone(), None)), vec![0]);
        assert_eq!(list_to_vec(merge_two_lists(None, l)), vec![0]);
    }

    #[test]
    fn test_iterative() {
        let l1 = build_list(vec![1, 2, 4]);
        let l2 = build_list(vec![1, 3, 4]);
        let merged = merge_two_lists_iterative(l1, l2);
        assert_eq!(list_to_vec(merged), vec![1, 1, 2, 3, 4, 4]);
    }
}
