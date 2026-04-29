/// LeetCode 50. Pow(x, n)
///
/// Implement `pow(x, n)`, which calculates `x` raised to the power `n`.
///
/// # Approach
/// Binary exponentiation (exponentiation by squaring).
/// Decompose `n` into binary form: n = Σ bᵢ · 2ⁱ.
/// Then xⁿ = Π x^(2ⁱ) for all i where bᵢ = 1.
///
/// # Correctness Proof
/// Invariant: result · base^exp = x^n (original values).
/// - Initialization: result = 1, base = x, exp = n → 1 · x^n = x^n.
/// - Maintenance:
///   * If exp is odd: result *= base, exp -= 1. Then result · base^exp remains unchanged.
///   * Then base *= base, exp /= 2. Since base becomes base² and exp halves,
///     base_new^exp_new = (base²)^(exp/2) = base^exp.
/// - Termination: exp = 0, so result = x^n.
///
/// # Complexity
/// - Time complexity: O(log |n|)
/// - Space complexity: O(1)

pub struct Solution;

impl Solution {
    pub fn my_pow(x: f64, n: i32) -> f64 {
        if n == 0 {
            return 1.0;
        }

        let mut base = x;
        let mut exp = n as i64; // Use i64 to handle i32::MIN safely
        let mut result = 1.0;

        if exp < 0 {
            base = 1.0 / base;
            exp = -exp;
        }

        while exp > 0 {
            if exp % 2 == 1 {
                result *= base;
            }
            base *= base;
            exp /= 2;
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let ans = Solution::my_pow(2.0, 10);
        assert!((ans - 1024.0).abs() < 1e-9);
    }

    #[test]
    fn test_example_2() {
        let ans = Solution::my_pow(2.1, 3);
        assert!((ans - 9.261).abs() < 1e-3);
    }

    #[test]
    fn test_negative_exponent() {
        let ans = Solution::my_pow(2.0, -2);
        assert!((ans - 0.25).abs() < 1e-9);
    }

    #[test]
    fn test_zero_exponent() {
        assert!((Solution::my_pow(0.0, 0) - 1.0).abs() < 1e-9);
        assert!((Solution::my_pow(99.0, 0) - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_negative_base() {
        let ans = Solution::my_pow(-2.0, 3);
        assert!((ans - (-8.0)).abs() < 1e-9);
    }

    #[test]
    fn test_min_int() {
        let ans = Solution::my_pow(2.0, i32::MIN);
        assert!(ans.is_finite());
    }
}
