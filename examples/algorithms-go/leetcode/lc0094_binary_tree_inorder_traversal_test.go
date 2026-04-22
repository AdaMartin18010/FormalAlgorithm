package leetcode

import (
	"testing"
)

func slicesEqual(a, b []int) bool {
	if len(a) != len(b) {
		return false
	}
	for i := range a {
		if a[i] != b[i] {
			return false
		}
	}
	return true
}

func buildTree123() *TreeNode {
	//     1
	//      \
	//       2
	//      /
	//     3
	return &TreeNode{
		Val: 1,
		Right: &TreeNode{
			Val:  2,
			Left: &TreeNode{Val: 3},
		},
	}
}

func buildCompleteTree() *TreeNode {
	//      4
	//     / \
	//    2   6
	//   / \ / \
	//  1  3 5  7
	return &TreeNode{
		Val: 4,
		Left: &TreeNode{
			Val:   2,
			Left:  &TreeNode{Val: 1},
			Right: &TreeNode{Val: 3},
		},
		Right: &TreeNode{
			Val:   6,
			Left:  &TreeNode{Val: 5},
			Right: &TreeNode{Val: 7},
		},
	}
}

func TestInorderTraversalRecursive(t *testing.T) {
	tests := []struct {
		root     *TreeNode
		expected []int
	}{
		{buildTree123(), []int{1, 3, 2}},
		{nil, nil},
		{&TreeNode{Val: 42}, []int{42}},
		{buildCompleteTree(), []int{1, 2, 3, 4, 5, 6, 7}},
	}

	for _, tt := range tests {
		result := InorderTraversalRecursive(tt.root)
		if !slicesEqual(result, tt.expected) {
			t.Errorf("InorderTraversalRecursive(...) = %v, want %v", result, tt.expected)
		}
	}
}

func TestInorderTraversalIterative(t *testing.T) {
	tests := []struct {
		root     *TreeNode
		expected []int
	}{
		{buildTree123(), []int{1, 3, 2}},
		{nil, []int{}},
		{&TreeNode{Val: 42}, []int{42}},
		{buildCompleteTree(), []int{1, 2, 3, 4, 5, 6, 7}},
	}

	for _, tt := range tests {
		result := InorderTraversalIterative(tt.root)
		if !slicesEqual(result, tt.expected) {
			t.Errorf("InorderTraversalIterative(...) = %v, want %v", result, tt.expected)
		}
	}
}
