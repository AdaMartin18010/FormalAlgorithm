package leetcode

// LeetCode 104 - Maximum Depth of Binary Tree
// https://leetcode.com/problems/maximum-depth-of-binary-tree/
//
// 题目：给定二叉树根节点，返回其最大深度。
//      最大深度是从根节点到最远叶子节点的最长路径上的节点数。
//
// 思路：递归。树的最大深度 = 1 + max(左子树深度, 右子树深度)。
// 时间复杂度：O(n)
// 空间复杂度：O(h)，h 为树高

type TreeNode struct {
	Val   int
	Left  *TreeNode
	Right *TreeNode
}

func maxDepth(root *TreeNode) int {
	if root == nil {
		return 0
	}
	leftDepth := maxDepth(root.Left)
	rightDepth := maxDepth(root.Right)
	if leftDepth > rightDepth {
		return 1 + leftDepth
	}
	return 1 + rightDepth
}
