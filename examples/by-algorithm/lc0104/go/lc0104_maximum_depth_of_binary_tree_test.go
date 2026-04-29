package leetcode

import "testing"

func TestMaxDepth(t *testing.T) {
	// 测试用例1：
	//      3
	//     / \
	//    9  20
	//      /  \
	//     15   7
	root1 := &TreeNode{Val: 3}
	root1.Left = &TreeNode{Val: 9}
	root1.Right = &TreeNode{Val: 20}
	root1.Right.Left = &TreeNode{Val: 15}
	root1.Right.Right = &TreeNode{Val: 7}
	if got := maxDepth(root1); got != 3 {
		t.Errorf("maxDepth() = %d, want 3", got)
	}

	// 测试用例2：空树
	if got := maxDepth(nil); got != 0 {
		t.Errorf("maxDepth(nil) = %d, want 0", got)
	}

	// 测试用例3：单节点
	root3 := &TreeNode{Val: 1}
	if got := maxDepth(root3); got != 1 {
		t.Errorf("maxDepth(single) = %d, want 1", got)
	}

	// 测试用例4：链式树
	root4 := &TreeNode{Val: 1}
	root4.Left = &TreeNode{Val: 2}
	root4.Left.Left = &TreeNode{Val: 3}
	root4.Left.Left.Left = &TreeNode{Val: 4}
	if got := maxDepth(root4); got != 4 {
		t.Errorf("maxDepth(chain) = %d, want 4", got)
	}
}
