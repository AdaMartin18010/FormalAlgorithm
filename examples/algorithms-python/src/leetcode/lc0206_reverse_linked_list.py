"""LeetCode 206. 反转链表 — Python 实现

给你单链表的头节点 head，请你反转链表，并返回反转后的链表。

对标: LeetCode 206 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md
"""

from typing import Optional


class ListNode:
    """单链表节点定义。"""

    def __init__(self, val: int = 0, next: Optional["ListNode"] = None):
        self.val = val
        self.next = next

    def to_list(self) -> list[int]:
        """将链表转换为 Python 列表（用于测试）。"""
        result = []
        node: Optional[ListNode] = self
        while node:
            result.append(node.val)
            node = node.next
        return result

    @staticmethod
    def from_list(values: list[int]) -> Optional["ListNode"]:
        """从 Python 列表构建链表。"""
        dummy = ListNode(0)
        tail = dummy
        for v in values:
            tail.next = ListNode(v)
            tail = tail.next
        return dummy.next


def reverse_list(head: Optional[ListNode]) -> Optional[ListNode]:
    """反转单链表。

    前置条件 (Pre):
        - head 为单链表的头节点，链表长度范围 [0, 5 * 10^4]。

    后置条件 (Post):
        - 返回原链表的反转链表头节点。
        - 原链表节点顺序完全倒置。

    核心思路:
        迭代法：维护 prev（已反转部分的头）和 curr（待反转的当前节点）。
        每次将 curr.next 指向 prev，然后 prev 和 curr 各前进一步。

    循环不变式:
        设 prev 为已反转链表的头节点，curr 为剩余未反转链表的头节点。
        则：
        1. 从 prev 出发沿 next 遍历得到原链表 [0..curr_prev] 的逆序。
        2. 从 curr 出发沿 next 遍历得到原链表 [curr..end] 的正序。

    复杂度:
        时间复杂度: O(n) — 遍历链表一次。
        空间复杂度: O(1) — 仅使用常数个额外指针。

    证明要点:
        - 初始化：prev = None, curr = head。
          已反转部分为空，不变式显然成立。
        - 保持：设 next_node = curr.next。
          curr.next = prev 后，curr 成为新的已反转部分的头。
          更新 prev = curr, curr = next_node，不变式保持。
        - 终止：curr = None 时，已反转部分包含全部节点，返回 prev。

    Args:
        head: 单链表头节点。

    Returns:
        反转后的链表头节点。
    """
    prev: Optional[ListNode] = None
    curr = head
    while curr:
        next_node = curr.next
        curr.next = prev
        prev = curr
        curr = next_node
    return prev


if __name__ == "__main__":
    # LeetCode 官方示例
    head1 = ListNode.from_list([1, 2, 3, 4, 5])
    rev1 = reverse_list(head1)
    assert rev1 is not None and rev1.to_list() == [5, 4, 3, 2, 1], "Example 1 failed"

    head2 = ListNode.from_list([1, 2])
    rev2 = reverse_list(head2)
    assert rev2 is not None and rev2.to_list() == [2, 1], "Example 2 failed"

    # 边界条件
    assert reverse_list(None) is None, "Empty list"
    head3 = ListNode.from_list([1])
    rev3 = reverse_list(head3)
    assert rev3 is not None and rev3.to_list() == [1], "Single element"

    head4 = ListNode.from_list(list(range(1_000)))
    rev4 = reverse_list(head4)
    assert rev4 is not None and rev4.to_list() == list(range(999, -1, -1)), "Large list"

    print("All tests passed.")
