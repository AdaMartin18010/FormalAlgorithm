package leetcode

// LeetCode 21 - Merge Two Sorted Lists
// https://leetcode.com/problems/merge-two-sorted-lists/
//
// 题目：合并两个非降序单链表，返回合并后的非降序链表头节点。
//
// 思路：虚拟头节点 + 双指针迭代。
//       每次比较两个链表的头节点，将较小者接到结果链表尾部。
// 时间复杂度：O(n + m)
// 空间复杂度：O(1)

type ListNode struct {
	Val  int
	Next *ListNode
}

func mergeTwoLists(l1 *ListNode, l2 *ListNode) *ListNode {
	dummy := &ListNode{Val: 0}
	tail := dummy

	for l1 != nil && l2 != nil {
		if l1.Val <= l2.Val {
			tail.Next = l1
			l1 = l1.Next
		} else {
			tail.Next = l2
			l2 = l2.Next
		}
		tail = tail.Next
	}

	// 连接剩余部分
	if l1 != nil {
		tail.Next = l1
	} else {
		tail.Next = l2
	}

	return dummy.Next
}
