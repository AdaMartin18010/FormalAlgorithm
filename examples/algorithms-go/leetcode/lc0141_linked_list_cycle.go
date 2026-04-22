// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// HasCycle 判断链表中是否存在环（Floyd 判圈算法）。
//
// 形式化规约：
//   Pre: head 为链表头节点，可能为 nil；链表长度 ∈ [0, 10^4]。
//   Post: 若链表存在环返回 true，否则返回 false。
//
// 循环不变式：
//   slow 每次走 1 步，fast 每次走 2 步。
//   若链表中存在环，则 slow 与 fast 最终必在环上相遇。
//
//   维护：
//   - 初始 slow = head, fast = head.Next（或 head）。
//   - 每轮：slow = slow.Next, fast = fast.Next.Next。
//   - 若 fast 或 fast.Next 为 nil，说明无环。
//   - 若 slow == fast，说明相遇，有环。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 相遇定理证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
//   - 关键引理：有环时，fast 相对 slow 的速度为 1 步/轮，必能追上。
func HasCycle(head *ListNode) bool {
	if head == nil || head.Next == nil {
		return false
	}

	slow := head
	fast := head.Next

	for slow != fast {
		if fast == nil || fast.Next == nil {
			return false
		}
		slow = slow.Next
		fast = fast.Next.Next
	}

	return true
}
