/// LeetCode 28 - Implement strStr()
/// https://leetcode.com/problems/implement-strstr/
///
/// 题目：返回 needle 在 haystack 中第一次出现的索引，若不存在则返回 -1。
///
/// 思路：KMP 算法。
///       1. 计算 needle 的前缀函数（pi 数组）
///       2. 利用 pi 数组在 haystack 上进行线性匹配
/// 时间复杂度：O(n + m)
/// 空间复杂度：O(m)

pub fn str_str(haystack: String, needle: String) -> i32 {
    if needle.is_empty() {
        return 0;
    }
    let n = haystack.len();
    let m = needle.len();
    if n < m {
        return -1;
    }

    let h: Vec<char> = haystack.chars().collect();
    let p: Vec<char> = needle.chars().collect();

    // 计算前缀函数
    let mut pi = vec![0; m];
    let mut k = 0;
    for q in 1..m {
        while k > 0 && p[k] != p[q] {
            k = pi[k - 1];
        }
        if p[k] == p[q] {
            k += 1;
        }
        pi[q] = k;
    }

    // KMP 匹配
    let mut q = 0;
    for i in 0..n {
        while q > 0 && p[q] != h[i] {
            q = pi[q - 1];
        }
        if p[q] == h[i] {
            q += 1;
        }
        if q == m {
            return (i + 1 - m) as i32;
        }
    }

    -1
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_str_str_found() {
        assert_eq!(str_str("hello".to_string(), "ll".to_string()), 2);
        assert_eq!(str_str("aaaaa".to_string(), "bba".to_string()), -1);
    }

    #[test]
    fn test_str_str_empty() {
        assert_eq!(str_str("".to_string(), "".to_string()), 0);
        assert_eq!(str_str("hello".to_string(), "".to_string()), 0);
        assert_eq!(str_str("".to_string(), "a".to_string()), -1);
    }

    #[test]
    fn test_str_str_overlap() {
        assert_eq!(str_str("aaaa".to_string(), "aa".to_string()), 0);
        assert_eq!(str_str("abcabcabc".to_string(), "abc".to_string()), 0);
    }

    #[test]
    fn test_str_str_not_found() {
        assert_eq!(str_str("abcdef".to_string(), "gh".to_string()), -1);
        assert_eq!(str_str("abc".to_string(), "abcd".to_string()), -1);
    }

    #[test]
    fn test_str_str_single_char() {
        assert_eq!(str_str("a".to_string(), "a".to_string()), 0);
        assert_eq!(str_str("abc".to_string(), "c".to_string()), 2);
    }
}
