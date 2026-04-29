"""LeetCode 23. 合并 K 个升序链表 — Python 实现（分治版本）

给你一个链表数组，每个链表都已经按升序排列。
请你将所有链表合并到一个升序链表中，返回合并后的链表。

对标: LeetCode 23 / docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
"""

from typing import List, Optional


class ListNode:
    """单链表节点。"""

    def __init__(self, val: int = 0, next: Optional["ListNode"] = None):
        self.val = val
        self.next = next

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, ListNode):
            return False
        return self.val == other.val and self.next == other.next


def merge_k_lists(lists: List[Optional[ListNode]]) -> Optional[ListNode]:
    """分治合并 k 个升序链表。

    前置条件 (Pre):
        - lists 包含 k 个已升序链表，k 范围 [0, 10^4]，总节点数不超过 10^5。

    后置条件 (Post):
        - 返回一个升序链表，包含所有输入链表中的全部节点。

    核心思路:
        分治合并：将 k 个链表两两配对合并，每轮链表数量减半。
        Round 1: k 个链表 → k/2 个链表
        Round 2: k/2 个链表 → k/4 个链表
        ...
        Round log k: 1 个链表

    复杂度:
        时间复杂度: O(N log k) — N 为总节点数，共 log k 轮合并。
        空间复杂度: O(log k) — 递归栈深度。

    证明要点:
        - 引理：合并两个有序链表的算法产生一个有序链表。
        - 对轮数进行归纳，每轮合并后链表仍然有序。
        - 经过 log k 轮后得到全局有序链表。

    Args:
        lists: k 个升序链表的头节点列表。

    Returns:
        合并后的升序链表头节点。
    """
    if not lists:
        return None
    return _merge_range(lists, 0, len(lists) - 1)


def _merge_range(lists: List[Optional[ListNode]], left: int, right: int) -> Optional[ListNode]:
    """分治合并 lists[left..right] 范围内的链表。"""
    if left == right:
        return lists[left]

    mid = left + (right - left) // 2
    l1 = _merge_range(lists, left, mid)
    l2 = _merge_range(lists, mid + 1, right)
    return _merge_two(l1, l2)


def _merge_two(l1: Optional[ListNode], l2: Optional[ListNode]) -> Optional[ListNode]:
    """合并两个有序链表。"""
    dummy = ListNode(0)
    tail = dummy

    while l1 and l2:
        if l1.val <= l2.val:
            tail.next = l1
            l1 = l1.next
        else:
            tail.next = l2
            l2 = l2.next
        tail = tail.next

    tail.next = l1 if l1 else l2
    return dummy.next


def _list_to_vec(head: Optional[ListNode]) -> List[int]:
    """辅助函数：链表转数组。"""
    result = []
    while head:
        result.append(head.val)
        head = head.next
    return result


def _vec_to_list(vals: List[int]) -> Optional[ListNode]:
    """辅助函数：数组转链表。"""
    dummy = ListNode(0)
    tail = dummy
    for v in vals:
        tail.next = ListNode(v)
        tail = tail.next
    return dummy.next


if __name__ == "__main__":
    # LeetCode 官方示例
    lists = [
        _vec_to_list([1, 4, 5]),
        _vec_to_list([1, 3, 4]),
        _vec_to_list([2, 6]),
    ]
    assert _list_to_vec(merge_k_lists(lists)) == [1, 1, 2, 3, 4, 4, 5, 6], "Example 1 failed"

    # 边界条件
    assert _list_to_vec(merge_k_lists([])) == [], "Empty lists"
    assert _list_to_vec(merge_k_lists([None, None])) == [], "All null"
    assert _list_to_vec(merge_k_lists([_vec_to_list([1])])) == [1], "Single list"

    print("All tests passed.")
