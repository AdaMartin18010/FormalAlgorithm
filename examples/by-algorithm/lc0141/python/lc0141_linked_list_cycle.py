"""LeetCode 141. 环形链表 — Python 实现

给定一个链表，判断链表中是否有环。

对标: LeetCode 141 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
"""

from typing import Optional


class ListNode:
    """链表节点定义。"""

    def __init__(self, x: int):
        self.val: int = x
        self.next: Optional["ListNode"] = None


def has_cycle(head: Optional[ListNode]) -> bool:
    """判断链表中是否存在环（Floyd 判圈算法）。

    前置条件 (Pre):
        - head 为链表头节点，可能为 None。
        - 链表长度 ∈ [0, 10^4]，节点值 ∈ [-10^5, 10^5]。
        - 若存在环，则环外节点数 + 环内节点数 ≤ 10^4。

    后置条件 (Post):
        - 若链表中存在环，返回 True。
        - 若链表中不存在环，返回 False。

    循环不变式:
        设慢指针 slow 每次走 1 步，快指针 fast 每次走 2 步。
        在每次迭代开始时（除第一次外），slow 与 fast 均已进入链表。
        若链表中存在环，则 slow 与 fast 最终必在环上相遇。

        维护：
        - 初始 slow = head, fast = head（或 head.next），不变式基础成立。
        - 每轮迭代：slow = slow.next, fast = fast.next.next。
        - 若 fast 或 fast.next 为 None，说明无环，返回 False。
        - 若 slow == fast，说明相遇，返回 True。

        终止推出：
        - 无环时 fast 走到末尾，循环终止，返回 False。
        - 有环时 slow == fast，循环终止，返回 True。

    复杂度:
        时间复杂度: O(n) — 无环时 fast 遍历最多 n 个节点；
                   有环时，设环外长度为 a，环长为 c，则 slow 进入环后
                   最多再走 c 步即与 fast 相遇，总计 O(a + c) = O(n)。
        空间复杂度: O(1) — 仅使用两个指针变量。

    证明要点:
        - 正确性证明（相遇定理）见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
        - 关键引理：若链表中存在环，快指针相对慢指针的速度为 1 步/轮，
          故在环内必能追上慢指针。

    Args:
        head: 链表头节点。

    Returns:
        若链表存在环返回 True，否则返回 False。
    """
    if head is None or head.next is None:
        return False

    slow = head
    fast = head.next

    while slow != fast:
        if fast is None or fast.next is None:
            return False
        slow = slow.next  # type: ignore[union-attr]
        fast = fast.next.next  # type: ignore[union-attr]

    return True


if __name__ == "__main__":
    # 示例 1：有环 [3,2,0,-4]，环入口为索引 1
    node1 = ListNode(3)
    node2 = ListNode(2)
    node3 = ListNode(0)
    node4 = ListNode(-4)
    node1.next = node2
    node2.next = node3
    node3.next = node4
    node4.next = node2  # 成环
    assert has_cycle(node1) is True, "Example 1 (cycle) failed"

    # 示例 2：无环 [1,2]
    node_a = ListNode(1)
    node_b = ListNode(2)
    node_a.next = node_b
    assert has_cycle(node_a) is False, "Example 2 (no cycle) failed"

    # 边界：空链表
    assert has_cycle(None) is False, "Empty list should have no cycle"

    # 边界：单节点无环
    single = ListNode(1)
    assert has_cycle(single) is False, "Single node no cycle"

    # 边界：单节点自环
    self_loop = ListNode(1)
    self_loop.next = self_loop
    assert has_cycle(self_loop) is True, "Self loop should be cycle"

    # 边界：两个节点成环
    n1 = ListNode(1)
    n2 = ListNode(2)
    n1.next = n2
    n2.next = n1
    assert has_cycle(n1) is True, "Two node cycle"

    print("All tests passed.")
