// LeetCode 94. Binary Tree Inorder Traversal
// https://leetcode.com/problems/binary-tree-inorder-traversal/
//
// Problem: Given the root of a binary tree, return its inorder traversal (left-root-right).
//
// Formal specification:
// - Pre: root is the root of a binary tree
// - Post: return list of node values in inorder sequence
//
// Algorithms:
// 1. Recursive DFS: recursively visit left subtree, current node, then right subtree.
// 2. Iterative: use an explicit stack to simulate recursion.
//
// Time: O(n), Space: O(h) where h is tree height.

package leetcode

// InorderTraversalRecursive returns inorder traversal using recursion.
func InorderTraversalRecursive(root *TreeNode) []int {
	var result []int
	var dfs func(node *TreeNode)
	dfs = func(node *TreeNode) {
		if node == nil {
			return
		}
		dfs(node.Left)
		result = append(result, node.Val)
		dfs(node.Right)
	}
	dfs(root)
	return result
}

// InorderTraversalIterative returns inorder traversal using an explicit stack.
func InorderTraversalIterative(root *TreeNode) []int {
	var result []int
	stack := []*TreeNode{}
	current := root

	for current != nil || len(stack) > 0 {
		for current != nil {
			stack = append(stack, current)
			current = current.Left
		}
		// Pop
		current = stack[len(stack)-1]
		stack = stack[:len(stack)-1]
		result = append(result, current.Val)
		current = current.Right
	}

	return result
}
