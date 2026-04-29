package leetcode

import "testing"

func TestDetectCycle(t *testing.T) {
	// 测试用例1：有环链表 3 -> 2 -> 0 -> -4 -> (回到 2)
	node3 := &ListNode{Val: 3}
	node2 := &ListNode{Val: 2}
	node0 := &ListNode{Val: 0}
	nodeNeg4 := &ListNode{Val: -4}
	node3.Next = node2
	node2.Next = node0
	node0.Next = nodeNeg4
	nodeNeg4.Next = node2

	if got := detectCycle(node3); got != node2 {
		t.Errorf("detectCycle() = %v, want %v", got, node2)
	}

	// 测试用例2：无环链表
	node1 := &ListNode{Val: 1}
	node1.Next = &ListNode{Val: 2}
	if got := detectCycle(node1); got != nil {
		t.Errorf("detectCycle() = %v, want nil", got)
	}

	// 测试用例3：自环
	nodeSelf := &ListNode{Val: 1}
	nodeSelf.Next = nodeSelf
	if got := detectCycle(nodeSelf); got != nodeSelf {
		t.Errorf("detectCycle() = %v, want self", got)
	}

	// 测试用例4：空链表
	if got := detectCycle(nil); got != nil {
		t.Errorf("detectCycle() = %v, want nil", got)
	}
}
