"""
LeetCode 206 - Reverse Linked List
https://leetcode.com/problems/reverse-linked-list/

题目：反转单链表，返回反转后的头节点。

思路：三指针迭代法。
      - prev: 已反转部分的头节点
      - curr: 当前待处理的节点
      - next_temp: 保存 curr.next 防止断链丢失
时间复杂度：O(n)
空间复杂度：O(1)
"""

from typing import Optional


class ListNode:
    def __init__(self, val: int = 0, next: Optional["ListNode"] = None):
        self.val = val
        self.next = next

    @staticmethod
    def from_list(vals: list[int]) -> Optional["ListNode"]:
        dummy = ListNode(0)
        curr = dummy
        for v in vals:
            curr.next = ListNode(v)
            curr = curr.next
        return dummy.next

    @staticmethod
    def to_list(head: Optional["ListNode"]) -> list[int]:
        result = []
        while head:
            result.append(head.val)
            head = head.next
        return result


class Solution:
    def reverseList(self, head: Optional[ListNode]) -> Optional[ListNode]:
        prev = None
        curr = head
        while curr:
            next_temp = curr.next  # 保存下一个节点
            curr.next = prev       # 反转指针方向
            prev = curr            # prev 前移
            curr = next_temp       # curr 前移
        return prev


def test_reverse_list():
    sol = Solution()

    # 测试用例1：普通链表
    head1 = ListNode.from_list([1, 2, 3, 4, 5])
    reversed1 = sol.reverseList(head1)
    assert ListNode.to_list(reversed1) == [5, 4, 3, 2, 1], "Test 1 failed"

    # 测试用例2：空链表
    assert sol.reverseList(None) is None, "Test 2 failed"

    # 测试用例3：单节点链表
    head3 = ListNode.from_list([1])
    reversed3 = sol.reverseList(head3)
    assert ListNode.to_list(reversed3) == [1], "Test 3 failed"

    # 测试用例4：双节点链表
    head4 = ListNode.from_list([1, 2])
    reversed4 = sol.reverseList(head4)
    assert ListNode.to_list(reversed4) == [2, 1], "Test 4 failed"

    print("All tests passed for LC 206 - Reverse Linked List")


if __name__ == "__main__":
    test_reverse_list()
