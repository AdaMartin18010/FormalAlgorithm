/// LeetCode 214. Shortest Palindrome
///
/// Given a string `s`, convert it to a palindrome by adding characters in front of it.
/// Return the shortest palindrome you can find.
///
/// # Approach
/// KMP prefix function (π array). Concatenate `s + "#" + reverse(s)`,
/// then compute the prefix function. The last value of π tells us the length
/// of the longest prefix of `s` that is also a suffix of the reversed string,
/// i.e., the longest palindromic prefix of `s`.
/// The remaining suffix `s[prefix_len..]` is reversed and prepended.
///
/// # Correctness Proof
/// Let `t = reverse(s)`. We need to find the longest prefix of `s` that is a palindrome.
/// A prefix `s[0..k]` is a palindrome iff `s[0..k] == reverse(s[0..k])`,
/// which is equivalent to `s[0..k]` being a prefix of `s` and a suffix of `t`.
/// The KMP prefix function on `s + "#" + t` computes exactly this maximum `k`.
/// After finding `k`, `s[k..]` is the non-palindromic suffix.
/// Prepending `reverse(s[k..])` makes the whole string a palindrome,
/// and it is shortest because any shorter palindrome would require a longer palindromic prefix.
///
/// # Complexity
/// - Time complexity: O(n)
/// - Space complexity: O(n)

pub struct Solution;

impl Solution {
    pub fn shortest_palindrome(s: String) -> String {
        if s.is_empty() {
            return s;
        }

        let rev: String = s.chars().rev().collect();
        let combined = format!("{}# {}", s, rev);
        let chars: Vec<char> = combined.chars().collect();
        let n = chars.len();

        // Compute KMP prefix function
        let mut pi = vec![0; n];
        for i in 1..n {
            let mut j = pi[i - 1];
            while j > 0 && chars[i] != chars[j] {
                j = pi[j - 1];
            }
            if chars[i] == chars[j] {
                j += 1;
            }
            pi[i] = j;
        }

        let prefix_len = pi[n - 1];
        let suffix: String = s.chars().skip(prefix_len).collect();
        let prefix_to_add: String = suffix.chars().rev().collect();
        format!("{}{}", prefix_to_add, s)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(Solution::shortest_palindrome("aacecaaa".to_string()), "aaacecaaa");
    }

    #[test]
    fn test_example_2() {
        assert_eq!(Solution::shortest_palindrome("abcd".to_string()), "dcbabcd");
    }

    #[test]
    fn test_empty() {
        assert_eq!(Solution::shortest_palindrome("".to_string()), "");
    }

    #[test]
    fn test_single_char() {
        assert_eq!(Solution::shortest_palindrome("a".to_string()), "a");
    }

    #[test]
    fn test_already_palindrome() {
        assert_eq!(Solution::shortest_palindrome("aba".to_string()), "aba");
        assert_eq!(Solution::shortest_palindrome("aa".to_string()), "aa");
    }

    #[test]
    fn test_all_same() {
        assert_eq!(Solution::shortest_palindrome("aaaa".to_string()), "aaaa");
    }
}
