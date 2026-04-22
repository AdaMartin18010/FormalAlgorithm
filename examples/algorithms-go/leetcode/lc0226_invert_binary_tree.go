package leetcode

// LeetCode 226 - Invert Binary Tree
// https://leetcode.com/problems/invert-binary-tree/
//
// Problem: Invert a binary tree (mirror).
//
// Approach: Recursive post-order traversal. Recursively invert left and right subtrees,
// then swap the left and right child pointers of the current node.
//
// Time: O(n), Space: O(h) where h is tree height.

// InvertTree inverts a binary tree and returns the new root.
func InvertTree(root *TreeNode) *TreeNode {
	if root == nil {
		return nil
	}

	left := InvertTree(root.Left)
	right := InvertTree(root.Right)

	root.Left = right
	root.Right = left

	return root
}
