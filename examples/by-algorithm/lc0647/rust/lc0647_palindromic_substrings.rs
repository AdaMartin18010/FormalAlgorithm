/// LeetCode 647. Palindromic Substrings
///
/// Given a string `s`, return the number of palindromic substrings in it.
/// A string is a palindrome when it reads the same backward as forward.
/// A substring is a contiguous sequence of characters within the string.
///
/// # Approach
/// Center expansion. For each possible center (2n-1 centers: n character centers
/// and n-1 gap centers between characters), expand outward while characters match.
/// Count each valid expansion as one palindromic substring.
///
/// # Correctness Proof
/// Every palindromic substring has a unique center (either a character for odd length,
/// or a gap for even length). The center expansion explores all possible centers,
/// and for each center, it expands as far as possible while the substring remains a palindrome.
/// Therefore, every palindromic substring is counted exactly once.
///
/// # Complexity
/// - Time complexity: O(n²)
/// - Space complexity: O(1)

pub struct Solution;

impl Solution {
    pub fn count_substrings(s: String) -> i32 {
        let bytes = s.as_bytes();
        let n = bytes.len();
        if n == 0 {
            return 0;
        }
        let mut count = 0;

        // Expand around each center
        for center in 0..(2 * n - 1) {
            let mut left = center / 2;
            let mut right = left + center % 2;

            while left < n && right < n && bytes[left] == bytes[right] {
                count += 1;
                if left == 0 {
                    break;
                }
                left -= 1;
                right += 1;
            }
        }

        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(Solution::count_substrings("abc".to_string()), 3);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(Solution::count_substrings("aaa".to_string()), 6);
    }

    #[test]
    fn test_empty() {
        assert_eq!(Solution::count_substrings("".to_string()), 0);
    }

    #[test]
    fn test_single_char() {
        assert_eq!(Solution::count_substrings("a".to_string()), 1);
    }

    #[test]
    fn test_two_same() {
        assert_eq!(Solution::count_substrings("aa".to_string()), 3); // "a", "a", "aa"
    }

    #[test]
    fn test_two_diff() {
        assert_eq!(Solution::count_substrings("ab".to_string()), 2); // "a", "b"
    }

    #[test]
    fn test_even_palindrome() {
        assert_eq!(Solution::count_substrings("abba".to_string()), 6); // "a","b","b","a","bb","abba"
    }
}
