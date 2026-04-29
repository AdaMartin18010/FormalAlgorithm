package leetcode

import (
	"reflect"
	"testing"
)

func inorder(root *TreeNode, out *[]int) {
	if root == nil {
		return
	}
	inorder(root.Left, out)
	*out = append(*out, root.Val)
	inorder(root.Right, out)
}

func TestInvertTree(t *testing.T) {
	// Example 1:
	//      4
	//     / \
	//    2   7
	//   / \ / \
	//  1  3 6  9
	root := &TreeNode{
		Val: 4,
		Left: &TreeNode{
			Val:   2,
			Left:  &TreeNode{Val: 1},
			Right: &TreeNode{Val: 3},
		},
		Right: &TreeNode{
			Val:   7,
			Left:  &TreeNode{Val: 6},
			Right: &TreeNode{Val: 9},
		},
	}

	inverted := InvertTree(root)
	var got []int
	inorder(inverted, &got)
	want := []int{9, 7, 6, 4, 3, 2, 1}
	if !reflect.DeepEqual(got, want) {
		t.Errorf("InvertTree example 1 inorder = %v, want %v", got, want)
	}

	// Empty tree
	if InvertTree(nil) != nil {
		t.Errorf("InvertTree(nil) should be nil")
	}

	// Single node
	single := &TreeNode{Val: 1}
	invSingle := InvertTree(single)
	var gotSingle []int
	inorder(invSingle, &gotSingle)
	wantSingle := []int{1}
	if !reflect.DeepEqual(gotSingle, wantSingle) {
		t.Errorf("InvertTree single node = %v, want %v", gotSingle, wantSingle)
	}
}
