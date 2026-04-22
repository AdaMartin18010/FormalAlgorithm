package leetcode

import "testing"

func TestDetectCycle(t *testing.T) {
	// 示例 1：有环 [3,2,0,-4]，环入口为索引 1（值为 2）
	node1 := &ListNode{Val: 3}
	node2 := &ListNode{Val: 2}
	node3 := &ListNode{Val: 0}
	node4 := &ListNode{Val: -4}
	node1.Next = node2
	node2.Next = node3
	node3.Next = node4
	node4.Next = node2
	if DetectCycle(node1) != node2 {
		t.Error("Expected cycle entry to be node2")
	}

	// 示例 2：无环 [1,2]
	nodeA := &ListNode{Val: 1}
	nodeB := &ListNode{Val: 2}
	nodeA.Next = nodeB
	if DetectCycle(nodeA) != nil {
		t.Error("Expected no cycle")
	}

	// 边界：空链表
	if DetectCycle(nil) != nil {
		t.Error("Expected nil for empty list")
	}

	// 边界：单节点自环
	selfLoop := &ListNode{Val: 1}
	selfLoop.Next = selfLoop
	if DetectCycle(selfLoop) != selfLoop {
		t.Error("Expected self as entry for self loop")
	}

	// 边界：两个节点成环
	n1 := &ListNode{Val: 1}
	n2 := &ListNode{Val: 2}
	n1.Next = n2
	n2.Next = n1
	if DetectCycle(n1) != n1 {
		t.Error("Expected n1 as entry for two node cycle")
	}
}
