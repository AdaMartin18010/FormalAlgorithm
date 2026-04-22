"""LeetCode 142. 环形链表 II — Python 实现

给定一个链表，返回链表开始入环的第一个节点；如果无环，返回 None。

对标: LeetCode 142 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
"""

from typing import Optional


class ListNode:
    """链表节点定义。"""

    def __init__(self, x: int):
        self.val: int = x
        self.next: Optional["ListNode"] = None


def detect_cycle(head: Optional[ListNode]) -> Optional[ListNode]:
    """返回链表环的入口节点（Floyd 判圈算法扩展）。

    前置条件 (Pre):
        - head 为链表头节点，可能为 None。
        - 链表长度 ∈ [0, 10^4]。

    后置条件 (Post):
        - 若链表存在环，返回环的入口节点。
        - 若链表不存在环，返回 None。

    循环不变式（阶段一：判断是否有环）:
        同 LC 141：slow 与 fast 在环内必相遇（若存在环）。

    循环不变式（阶段二：定位入口）:
        设相遇点为 M，令指针 p1 从 head 出发，p2 从 M 出发，均每次走 1 步。
        则 p1 与 p2 必在环入口相遇。

        维护：
        - 设环外长度为 a，环入口到相遇点距离为 b，相遇点回到入口距离为 c。
        - 阶段一结束时：slow 走了 a + b 步，fast 走了 a + b + k(b + c) = 2(a + b) 步。
        - 故 a + b = k(b + c)，即 a = k(b + c) - b = (k-1)(b+c) + c。
        - 因此从 head 走 a 步 = 从 M 走 (k-1) 圈 + c 步，两者恰在入口相遇。

    复杂度:
        时间复杂度: O(n) — 阶段一 O(n)，阶段二 O(a) ≤ O(n)。
        空间复杂度: O(1) — 仅使用若干指针变量。

    证明要点:
        - 入口定位证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
        - 核心等式：a = (k-1)(b+c) + c，保证两指针同步走必在入口相遇。

    Args:
        head: 链表头节点。

    Returns:
        环的入口节点，若无环返回 None。
    """
    if head is None or head.next is None:
        return None

    # 阶段一：判断是否有环并找到相遇点
    slow = head
    fast = head

    while True:
        if fast is None or fast.next is None:
            return None
        slow = slow.next  # type: ignore[union-attr]
        fast = fast.next.next  # type: ignore[union-attr]
        if slow == fast:
            break

    # 阶段二：定位环入口
    ptr1 = head
    ptr2 = slow
    while ptr1 != ptr2:
        ptr1 = ptr1.next  # type: ignore[union-attr]
        ptr2 = ptr2.next  # type: ignore[union-attr]

    return ptr1


if __name__ == "__main__":
    # 示例 1：有环 [3,2,0,-4]，环入口为索引 1（值为 2）
    node1 = ListNode(3)
    node2 = ListNode(2)
    node3 = ListNode(0)
    node4 = ListNode(-4)
    node1.next = node2
    node2.next = node3
    node3.next = node4
    node4.next = node2
    assert detect_cycle(node1) is node2, "Example 1 failed"

    # 示例 2：无环 [1,2]
    node_a = ListNode(1)
    node_b = ListNode(2)
    node_a.next = node_b
    assert detect_cycle(node_a) is None, "Example 2 (no cycle) failed"

    # 边界：空链表
    assert detect_cycle(None) is None, "Empty list"

    # 边界：单节点自环
    self_loop = ListNode(1)
    self_loop.next = self_loop
    assert detect_cycle(self_loop) is self_loop, "Self loop"

    # 边界：两个节点成环
    n1 = ListNode(1)
    n2 = ListNode(2)
    n1.next = n2
    n2.next = n1
    assert detect_cycle(n1) is n1, "Two node cycle"

    print("All tests passed.")
