//! LeetCode 3. 无重复字符的最长子串
//!
//! 给定一个字符串 s，找出其中不含有重复字符的最长子串的长度。
//!
//! 对标: LeetCode 3 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md

use std::collections::HashMap;

/// 计算不含重复字符的最长子串长度。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`s` 为字符串，长度 ∈ [0, 5 * 10^4]。
/// - **后置条件 (Post)**：返回 max_{0 ≤ l ≤ r < n} (r - l + 1)，其中 s[l..r] 不含重复字符。
///   若 s 为空，返回 0。
///
/// # 核心思路
///
/// 滑动窗口：维护窗口 [left, right]，保证窗口内无重复字符。
/// 使用哈希表记录每个字符最后出现的位置。
/// 当发现重复字符时，将 left 收缩到重复字符上次出现位置的右侧。
///
/// # 窗口不变式 WindowInvariant(left, right)
///
/// s[left..right] 中所有字符均唯一。
///
/// **维护**：
/// - 初始 left = 0，窗口为空或仅含一个字符，不变式成立。
/// - 扩展 right：考察 s[right]。
///   * 若 s[right] 不在窗口中（或上次出现位置 < left），直接扩展。
///   * 若 s[right] 在窗口中，将 left 移动到上次出现位置 + 1，保证新窗口内无重复。
/// - 更新 s[right] 的最后出现位置。
///
/// **终止推出**：right 遍历完所有字符，期间记录的最大窗口大小即为答案。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n) — right 指针遍历字符串一次，left 指针最多移动 n 次。
/// - **空间复杂度**：O(min(m, n)) — m 为字符集大小，哈希表最多存储窗口内字符。
///   ASCII 字符集下为 O(1)。
///
/// # 证明要点
///
/// - 不遗漏最优解的证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md`
/// - 核心：任何最优子串的右端点必被 right 指针访问到，此时 left 已收缩到
///   保证窗口内无重复的最左位置，故该子串必被考察。
pub fn length_of_longest_substring(s: String) -> i32 {
    let mut char_index: HashMap<char, usize> = HashMap::new();
    let mut max_len: usize = 0;
    let mut left: usize = 0;

    for (right, ch) in s.chars().enumerate() {
        if let Some(&last_pos) = char_index.get(&ch) {
            if last_pos >= left {
                left = last_pos + 1;
            }
        }
        char_index.insert(ch, right);
        max_len = max_len.max(right - left + 1);
    }

    max_len as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(length_of_longest_substring("abcabcbb".to_string()), 3);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(length_of_longest_substring("bbbbb".to_string()), 1);
    }

    #[test]
    fn test_example_3() {
        assert_eq!(length_of_longest_substring("pwwkew".to_string()), 3);
    }

    #[test]
    fn test_empty() {
        assert_eq!(length_of_longest_substring("".to_string()), 0);
    }

    #[test]
    fn test_single_char() {
        assert_eq!(length_of_longest_substring("a".to_string()), 1);
    }

    #[test]
    fn test_all_distinct() {
        assert_eq!(length_of_longest_substring("abcdef".to_string()), 6);
    }

    #[test]
    fn test_scattered_repeats() {
        assert_eq!(length_of_longest_substring("abba".to_string()), 2);
    }

    #[test]
    fn test_special_chars() {
        assert_eq!(length_of_longest_substring(" !@# !@#$".to_string()), 5);
    }
}
