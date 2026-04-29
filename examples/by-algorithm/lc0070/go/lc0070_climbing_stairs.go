// LeetCode 70. Climbing Stairs
// https://leetcode.com/problems/climbing-stairs/
//
// Problem: You are climbing a staircase. It takes n steps to reach the top.
// Each time you can either climb 1 or 2 steps. In how many distinct ways can you climb?
//
// Formal specification:
// - Pre: n >= 0
// - Post: result = f(n) where f(0)=1, f(1)=1, f(n)=f(n-1)+f(n-2)
//
// Algorithm: DP with optimal substructure. f(n) = fib(n+1).
// Proof by induction: see Lean proof.
//
// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
// Lean proof: examples/lean_proofs/leetcode/lc0070_climbing_stairs.lean

package leetcode

func ClimbStairs(n int) int {
	if n <= 1 {
		return 1
	}

	prev2 := 1 // f(0)
	prev1 := 1 // f(1)

	for i := 2; i <= n; i++ {
		curr := prev1 + prev2
		prev2 = prev1
		prev1 = curr
	}

	return prev1
}
