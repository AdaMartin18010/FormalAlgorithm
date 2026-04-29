// LeetCode 1. Two Sum
// https://leetcode.com/problems/two-sum/
//
// Problem: Given an array of integers nums and an integer target,
// return indices of the two numbers such that they add up to target.
//
// Formal specification:
// - Pre: exactly one solution exists, cannot use same element twice
// - Post: result = [i, j] where i < j and nums[i] + nums[j] = target
//
// Algorithm: Hash map one-pass. For each element, check if complement exists in map.
// Time: O(n), Space: O(n).
//
// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/01-哈希表.md
// Lean proof: examples/lean_proofs/leetcode/lc0001_two_sum.lean

package leetcode

func TwoSum(nums []int, target int) []int {
	seen := make(map[int]int) // value -> index

	for j, current := range nums {
		complement := target - current
		if i, ok := seen[complement]; ok {
			return []int{i, j}
		}
		seen[current] = j
	}

	return nil // no solution found (should not happen per problem constraints)
}
