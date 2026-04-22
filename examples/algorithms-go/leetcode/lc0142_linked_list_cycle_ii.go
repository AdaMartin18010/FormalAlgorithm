package leetcode

// LeetCode 142 - Linked List Cycle II
// https://leetcode.com/problems/linked-list-cycle-ii/
//
// 题目：给定一个链表的头节点 head，返回链表开始入环的第一个节点。
//      如果链表无环，则返回 nil。
//
// 思路：Floyd 判圈算法（龟兔赛跑）。
//       阶段一：快慢指针找相遇点。
//       阶段二：一个指针从头出发，一个从相遇点出发，同速前进，相遇点即为环入口。
// 时间复杂度：O(n)
// 空间复杂度：O(1)

func detectCycle(head *ListNode) *ListNode {
	if head == nil || head.Next == nil {
		return nil
	}

	// 阶段一：找相遇点
	slow, fast := head, head
	for fast != nil && fast.Next != nil {
		slow = slow.Next
		fast = fast.Next.Next
		if slow == fast {
			break
		}
	}

	// 无环
	if fast == nil || fast.Next == nil {
		return nil
	}

	// 阶段二：找环入口
	ptr := head
	for ptr != slow {
		ptr = ptr.Next
		slow = slow.Next
	}

	return ptr
}
