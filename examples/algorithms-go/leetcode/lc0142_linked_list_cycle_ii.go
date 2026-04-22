// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
package leetcode

// DetectCycle 返回链表环的入口节点（Floyd 判圈算法扩展）。
//
// 形式化规约：
//   Pre: head 为链表头节点，可能为 nil；链表长度 ∈ [0, 10^4]。
//   Post: 若链表存在环，返回环的入口节点；否则返回 nil。
//
// 循环不变式（阶段一）：
//   同 LC 141：slow 与 fast 在环内必相遇（若存在环）。
//
// 循环不变式（阶段二）：
//   设相遇点为 M，p1 从 head 出发，p2 从 M 出发，均每次走 1 步。
//   则 p1 与 p2 必在环入口相遇。
//
//   证明：设环外长度为 a，环入口到相遇点距离为 b，相遇点回到入口为 c。
//   阶段一结束时：slow 走了 a+b，fast 走了 a+b+k(b+c) = 2(a+b)。
//   故 a = (k-1)(b+c) + c，即从 head 走 a 步 = 从 M 走 (k-1) 圈 + c 步，恰在入口相遇。
//
// 复杂度：
//   时间复杂度: O(n)
//   空间复杂度: O(1)
//
// 证明要点：
//   - 入口定位证明见 docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md
func DetectCycle(head *ListNode) *ListNode {
	if head == nil || head.Next == nil {
		return nil
	}

	// 阶段一：判断是否有环并找到相遇点
	slow := head
	fast := head

	for {
		if fast == nil || fast.Next == nil {
			return nil
		}
		slow = slow.Next
		fast = fast.Next.Next
		if slow == fast {
			break
		}
	}

	// 阶段二：定位环入口
	ptr1 := head
	ptr2 := slow
	for ptr1 != ptr2 {
		ptr1 = ptr1.Next
		ptr2 = ptr2.Next
	}

	return ptr1
}
