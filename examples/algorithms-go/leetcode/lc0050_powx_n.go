// LeetCode 50. Pow(x, n)
// https://leetcode.com/problems/powx-n/
//
// Problem: Implement pow(x, n), which calculates x raised to the power n.
//
// Formal specification:
// - Pre: x ∈ R, n ∈ Z
// - Post: return x^n
//
// Algorithm: Binary exponentiation (exponentiation by squaring).
// Decompose n into binary: n = Σ bᵢ·2ⁱ, then xⁿ = Π x^(2ⁱ) for all bᵢ=1.
//
// Time: O(log |n|), Space: O(1).

package leetcode

// MyPow calculates x raised to the power n.
func MyPow(x float64, n int) float64 {
	if n == 0 {
		return 1.0
	}

	base := x
	exp := int64(n) // use i64 to safely handle math.MinInt32
	result := 1.0

	if exp < 0 {
		base = 1.0 / base
		exp = -exp
	}

	for exp > 0 {
		if exp%2 == 1 {
			result *= base
		}
		base *= base
		exp /= 2
	}

	return result
}
