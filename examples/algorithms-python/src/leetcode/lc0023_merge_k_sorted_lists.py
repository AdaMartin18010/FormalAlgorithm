"""LeetCode 23. 合并 K 个升序链表 — Python 实现

给你一个链表数组，每个链表都已经按升序排列。
请你将所有链表合并到一个升序链表中，返回合并后的链表。

对标: LeetCode 23 / docs/13-LeetCode算法面试专题/06-面试专题/01-高频Top100-数组与链表.md
"""

from typing import Optional
import heapq


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


# 为 ListNode 定义比较方法以支持 heapq
ListNode.__lt__ = lambda self, other: self.val < other.val  # type: ignore[method-assign]


def merge_k_lists(lists: list[Optional[ListNode]]) -> Optional[ListNode]:
    """合并 K 个升序链表。

    前置条件 (Pre):
        - lists 包含 k 个已按升序排列的单链表，k 范围 [0, 10^4]。
        - 所有链表节点总数不超过 10^5，节点值范围 [-10^4, 10^4]。

    后置条件 (Post):
        - 返回一个升序链表，包含所有输入链表中的全部节点。

    核心思路:
        最小堆法：维护一个大小为 k 的最小堆，存储每个链表的当前头节点。
        每次从堆顶取出最小元素加入结果链表，并将该元素所在链表的下一个节点入堆。

    复杂度:
        时间复杂度: O(N log k) — N 为总节点数，每次堆操作 O(log k)。
        空间复杂度: O(k) — 堆中最多同时存在 k 个元素。

    证明要点:
        - 不变式：堆中始终包含每个非空输入链表的当前最小未处理节点。
        - 每次取出的节点 val 不大于堆中任何其他节点，因此按取出顺序链接
          得到的链表是全局升序的。
        - 终止时所有节点均被取出并链接，结果链表包含全部 N 个节点。

    Args:
        lists: K 个升序链表的头节点列表。

    Returns:
        合并后的升序链表头节点。
    """
    heap: list[tuple[int, int, ListNode]] = []
    for idx, node in enumerate(lists):
        if node:
            heapq.heappush(heap, (node.val, idx, node))

    dummy = ListNode(0)
    tail = dummy

    while heap:
        val, idx, node = heapq.heappop(heap)
        tail.next = node
        tail = tail.next
        if node.next:
            heapq.heappush(heap, (node.next.val, idx, node.next))

    return dummy.next


if __name__ == "__main__":
    # LeetCode 官方示例
    lists1 = [
        ListNode.from_list([1, 4, 5]),
        ListNode.from_list([1, 3, 4]),
        ListNode.from_list([2, 6]),
    ]
    merged1 = merge_k_lists(lists1)
    assert merged1 is not None and merged1.to_list() == [1, 1, 2, 3, 4, 4, 5, 6], "Example 1 failed"

    assert merge_k_lists([]) is None, "Empty lists"
    assert merge_k_lists([None, None]) is None, "All null lists"

    lists2 = [ListNode.from_list([])]
    merged2 = merge_k_lists(lists2)
    assert merged2 is None, "Single empty list"

    lists3 = [ListNode.from_list([1]), ListNode.from_list([0])]
    merged3 = merge_k_lists(lists3)
    assert merged3 is not None and merged3.to_list() == [0, 1], "Two single-node lists"

    print("All tests passed.")
