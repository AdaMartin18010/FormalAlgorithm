// Package leetcode 提供 LeetCode 经典题目的 Go 实现。
//
// 正确性证明与复杂度分析参见：
//
//	docs/13-LeetCode算法面试专题/02-算法范式专题/06-分治.md
package leetcode

// ListNode 单链表节点。
type ListNode struct {
	Val  int
	Next *ListNode
}

// MergeKLists 分治合并 k 个升序链表。
//
// 形式化规约：
//   Pre: lists 包含 k 个已升序链表。
//   Post: 返回一个升序链表，包含所有输入链表中的全部节点。
//
// 核心思路：
//   分治合并：将 k 个链表两两配对合并，每轮链表数量减半。
//
// 复杂度：
//   时间复杂度: O(N log k)
//   空间复杂度: O(log k)
func MergeKLists(lists []*ListNode) *ListNode {
	n := len(lists)
	if n == 0 {
		return nil
	}
	return mergeRange(lists, 0, n-1)
}

func mergeRange(lists []*ListNode, left, right int) *ListNode {
	if left == right {
		return lists[left]
	}
	mid := left + (right-left)/2
	l1 := mergeRange(lists, left, mid)
	l2 := mergeRange(lists, mid+1, right)
	return mergeTwo(l1, l2)
}

func mergeTwo(l1, l2 *ListNode) *ListNode {
	dummy := &ListNode{}
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

	if l1 != nil {
		tail.Next = l1
	} else {
		tail.Next = l2
	}

	return dummy.Next
}
