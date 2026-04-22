/// LeetCode 9. Palindrome Number
///
/// Given an integer `x`, return `true` if `x` is a palindrome, and `false` otherwise.
///
/// Follow up: Could you solve it without converting the integer to a string?
///
/// # Approach
/// Reverse half of the number and compare it with the other half.
/// This avoids overflow issues that would occur when reversing the entire number.
///
/// # Complexity
/// - Time complexity: O(log₁₀ n) — number of digits divided by 2
/// - Space complexity: O(1)

pub struct Solution;

impl Solution {
    pub fn is_palindrome(x: i32) -> bool {
        // Negative numbers are not palindromes
        if x < 0 {
            return false;
        }

        // Single digit numbers are palindromes
        if x < 10 {
            return true;
        }

        // Numbers ending in 0 (except 0 itself) are not palindromes
        if x % 10 == 0 {
            return false;
        }

        let mut x = x;
        let mut reversed = 0;

        while x > reversed {
            reversed = reversed * 10 + x % 10;
            x /= 10;
        }

        // For even-length numbers: x == reversed
        // For odd-length numbers: x == reversed / 10 (middle digit is ignored)
        x == reversed || x == reversed / 10
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(Solution::is_palindrome(121));
    }

    #[test]
    fn test_example_2() {
        assert!(!Solution::is_palindrome(-121));
    }

    #[test]
    fn test_example_3() {
        assert!(!Solution::is_palindrome(10));
    }

    #[test]
    fn test_single_digit() {
        assert!(Solution::is_palindrome(0));
        assert!(Solution::is_palindrome(5));
    }

    #[test]
    fn test_even_digits() {
        assert!(Solution::is_palindrome(1221));
        assert!(!Solution::is_palindrome(1234));
    }

    #[test]
    fn test_large_palindrome() {
        assert!(Solution::is_palindrome(123_454_321));
    }

    #[test]
    fn test_overflow_risk() {
        // 2_147_483_647 reversed would overflow i32
        assert!(!Solution::is_palindrome(2_147_483_647));
    }
}
