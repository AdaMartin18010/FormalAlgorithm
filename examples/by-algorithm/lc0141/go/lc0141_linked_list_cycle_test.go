package leetcode

import "testing"

func TestHasCycle(t *testing.T) {
	// 示例 1：有环 [3,2,0,-4]，环入口为索引 1
	node1 := &ListNode{Val: 3}
	node2 := &ListNode{Val: 2}
	node3 := &ListNode{Val: 0}
	node4 := &ListNode{Val: -4}
	node1.Next = node2
	node2.Next = node3
	node3.Next = node4
	node4.Next = node2
	if !HasCycle(node1) {
		t.Error("Expected cycle for example 1")
	}

	// 示例 2：无环 [1,2]
	nodeA := &ListNode{Val: 1}
	nodeB := &ListNode{Val: 2}
	nodeA.Next = nodeB
	if HasCycle(nodeA) {
		t.Error("Expected no cycle for example 2")
	}

	// 边界：空链表
	if HasCycle(nil) {
		t.Error("Expected no cycle for nil")
	}

	// 边界：单节点无环
	single := &ListNode{Val: 1}
	if HasCycle(single) {
		t.Error("Expected no cycle for single node")
	}

	// 边界：单节点自环
	selfLoop := &ListNode{Val: 1}
	selfLoop.Next = selfLoop
	if !HasCycle(selfLoop) {
		t.Error("Expected cycle for self loop")
	}

	// 边界：两个节点成环
	n1 := &ListNode{Val: 1}
	n2 := &ListNode{Val: 2}
	n1.Next = n2
	n2.Next = n1
	if !HasCycle(n1) {
		t.Error("Expected cycle for two node cycle")
	}
}
