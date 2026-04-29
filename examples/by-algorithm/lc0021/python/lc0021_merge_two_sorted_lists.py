"""
LeetCode 21. Merge Two Sorted Lists
https://leetcode.com/problems/merge-two-sorted-lists/

Problem: Merge two sorted linked lists and return it as a new sorted list.
The new list should be made by splicing together the nodes of the first two lists.

Formal specification:
- Pre: l1 and l2 are sorted in non-decreasing order
- Post: result is sorted and contains exactly the multiset union of l1 and l2

Algorithm: Recursive merge with O(n+m) time, O(n+m) space (call stack).
Iterative version uses O(1) extra space.

Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/06-双指针.md
Lean proof: examples/lean_proofs/leetcode/lc0021_merge_two_sorted_lists.lean
"""

from typing import Optional


class ListNode:
    def __init__(self, val: int = 0, next: Optional["ListNode"] = None):
        self.val = val
        self.next = next

    def __repr__(self) -> str:
        return f"ListNode({self.val})"


def merge_two_lists(
    list1: Optional[ListNode], list2: Optional[ListNode]
) -> Optional[ListNode]:
    """Recursive merge of two sorted linked lists."""
    if not list1:
        return list2
    if not list2:
        return list1

    if list1.val <= list2.val:
        list1.next = merge_two_lists(list1.next, list2)
        return list1
    else:
        list2.next = merge_two_lists(list1, list2.next)
        return list2


def merge_two_lists_iterative(
    list1: Optional[ListNode], list2: Optional[ListNode]
) -> Optional[ListNode]:
    """Iterative merge with O(1) extra space."""
    dummy = ListNode(0)
    tail = dummy

    while list1 and list2:
        if list1.val <= list2.val:
            tail.next = list1
            list1 = list1.next
        else:
            tail.next = list2
            list2 = list2.next
        tail = tail.next

    tail.next = list1 if list1 else list2
    return dummy.next


def build_list(vals: list[int]) -> Optional[ListNode]:
    if not vals:
        return None
    head = ListNode(vals[0])
    curr = head
    for v in vals[1:]:
        curr.next = ListNode(v)
        curr = curr.next
    return head


def list_to_vec(head: Optional[ListNode]) -> list[int]:
    res = []
    while head:
        res.append(head.val)
        head = head.next
    return res


if __name__ == "__main__":
    # Test case 1
    l1 = build_list([1, 2, 4])
    l2 = build_list([1, 3, 4])
    merged = merge_two_lists(l1, l2)
    assert list_to_vec(merged) == [1, 1, 2, 3, 4, 4]

    # Test case 2: empty lists
    assert list_to_vec(merge_two_lists(None, None)) == []
    assert list_to_vec(merge_two_lists(build_list([0]), None)) == [0]

    # Test iterative version
    l1 = build_list([1, 2, 4])
    l2 = build_list([1, 3, 4])
    merged = merge_two_lists_iterative(l1, l2)
    assert list_to_vec(merged) == [1, 1, 2, 3, 4, 4]

    print("All tests passed for LC 21.")
