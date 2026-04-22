/// LeetCode 5 - Longest Palindromic Substring
/// https://leetcode.com/problems/longest-palindromic-substring/
///
/// 题目：给定字符串 s，找到 s 中最长的回文子串。
///
/// 思路：中心扩展法。
///       枚举 2n-1 个中心（n 个字符中心 + n-1 个间隙中心），
///       向两侧扩展直到不再回文，记录最长回文。
/// 时间复杂度：O(n^2)
/// 空间复杂度：O(1)

pub fn longest_palindrome(s: String) -> String {
    let bytes = s.as_bytes();
    let n = bytes.len();
    if n == 0 {
        return String::new();
    }

    let mut start = 0;
    let mut max_len = 1;

    // 闭包：从 left, right 向两侧扩展，返回回文长度
    let expand = |left: i32, right: i32| -> i32 {
        let mut l = left;
        let mut r = right;
        while l >= 0 && r < n as i32 && bytes[l as usize] == bytes[r as usize] {
            l -= 1;
            r += 1;
        }
        r - l - 1
    };

    for i in 0..n {
        let len1 = expand(i as i32, i as i32);       // 奇数长度
        let len2 = expand(i as i32, i as i32 + 1);   // 偶数长度
        let len = len1.max(len2);
        if len > max_len as i32 {
            max_len = len as usize;
            start = i - (len as usize - 1) / 2;
        }
    }

    s[start..start + max_len].to_string()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_longest_palindrome_odd() {
        assert_eq!(longest_palindrome("babad".to_string()), "bab");
    }

    #[test]
    fn test_longest_palindrome_even() {
        assert_eq!(longest_palindrome("cbbd".to_string()), "bb");
    }

    #[test]
    fn test_longest_palindrome_single() {
        assert_eq!(longest_palindrome("a".to_string()), "a");
    }

    #[test]
    fn test_longest_palindrome_all_same() {
        assert_eq!(longest_palindrome("aaaa".to_string()), "aaaa");
    }

    #[test]
    fn test_longest_palindrome_no_repeat() {
        assert_eq!(longest_palindrome("abc".to_string()), "a");
    }

    #[test]
    fn test_longest_palindrome_long() {
        assert_eq!(
            longest_palindrome("forgeeksskeegfor".to_string()),
            "geeksskeeg"
        );
    }
}
