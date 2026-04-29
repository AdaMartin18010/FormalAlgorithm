//! LeetCode 76. 最小覆盖子串
//!
//! 给你一个字符串 s、一个字符串 t，返回 s 中涵盖 t 所有字符的最小子串。
//! 如果不存在符合条件的子串，返回空字符串 ""。
//!
//! 对标: LeetCode 76 / docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md

use std::collections::HashMap;

/// 找出 s 中涵盖 t 所有字符的最小子串。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`s`, `t` 由大写/小写英文字母组成；len(s), len(t) ∈ [1, 10^5]。
/// - **后置条件 (Post)**：返回 s 的最短子串 substr，使得 t 中每个字符在 substr 中
///   出现次数均不少于在 t 中的出现次数；若不存在返回空字符串。
///
/// # 核心思路
///
/// 滑动窗口 + 双哈希表：
/// - need：记录 t 中各字符的需求量。
/// - window：记录当前窗口中各字符的实际数量。
/// - valid：记录窗口中满足需求（数量 ≥ need）的字符种类数。
///
/// 当 valid == len(need) 时，窗口已覆盖 t，尝试收缩 left 寻找更短窗口。
///
/// # 窗口不变式 WindowInvariant(left, right)
///
/// window 准确记录 s[left..right] 中各字符的出现次数。
/// valid 等于 window[ch] ≥ need[ch] 的字符种类数（只考虑 need 中的字符）。
///
/// **维护**：
/// - 扩展 right：将 s[right] 加入 window。
///   * 若该字符在 need 中且 window[ch] == need[ch]，valid += 1。
/// - 当 valid == len(need) 时（窗口已覆盖 t），尝试收缩 left：
///   * 更新最小窗口记录。
///   * 将 s[left] 移出 window。
///   * 若移出的是 need 中字符且 window[ch] < need[ch]，valid -= 1。
///   * left += 1，继续尝试收缩。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(|s| + |t|) — 摊还分析：right 遍历 s 一次，left 最多移动 |s| 次。
/// - **空间复杂度**：O(|Σ|) = O(1) — 字符集大小为 52（大小写字母）。
///
/// # 证明要点
///
/// - 窗口收缩正确性见 `docs/13-LeetCode算法面试专题/02-算法范式专题/03-滑动窗口.md`
/// - 核心：当窗口已覆盖 t 时，收缩左边界不会丢失最优性，
///   因为更短的窗口仍可能满足覆盖条件。
pub fn min_window(s: String, t: String) -> String {
    if s.is_empty() || t.is_empty() {
        return String::new();
    }

    // need 记录 t 中各字符需求量
    let mut need: HashMap<char, i32> = HashMap::new();
    for ch in t.chars() {
        *need.entry(ch).or_insert(0) += 1;
    }

    let need_count = need.len();
    let mut window: HashMap<char, i32> = HashMap::new();
    let mut valid = 0;
    let mut left = 0;
    let mut start = 0;
    let mut min_len = usize::MAX;

    let s_chars: Vec<char> = s.chars().collect();

    for right in 0..s_chars.len() {
        let ch = s_chars[right];
        *window.entry(ch).or_insert(0) += 1;
        if let Some(&cnt) = need.get(&ch) {
            if window[&ch] == cnt {
                valid += 1;
            }
        }

        // 尝试收缩窗口
        while valid == need_count {
            if right - left + 1 < min_len {
                min_len = right - left + 1;
                start = left;
            }

            let left_ch = s_chars[left];
            if let Some(&cnt) = window.get(&left_ch) {
                let new_cnt = cnt - 1;
                window.insert(left_ch, new_cnt);
                if let Some(&need_cnt) = need.get(&left_ch) {
                    if new_cnt < need_cnt {
                        valid -= 1;
                    }
                }
            }
            left += 1;
        }
    }

    if min_len == usize::MAX {
        String::new()
    } else {
        s_chars[start..start + min_len].iter().collect()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(
            min_window("ADOBECODEBANC".to_string(), "ABC".to_string()),
            "BANC"
        );
    }

    #[test]
    fn test_example_2() {
        assert_eq!(min_window("a".to_string(), "a".to_string()), "a");
    }

    #[test]
    fn test_example_3() {
        assert_eq!(min_window("a".to_string(), "aa".to_string()), "");
    }

    #[test]
    fn test_same_strings() {
        assert_eq!(min_window("abc".to_string(), "abc".to_string()), "abc");
    }

    #[test]
    fn test_at_beginning() {
        assert_eq!(min_window("abcdef".to_string(), "abc".to_string()), "abc");
    }

    #[test]
    fn test_at_end() {
        assert_eq!(min_window("xyzabc".to_string(), "abc".to_string()), "abc");
    }

    #[test]
    fn test_case_sensitive() {
        assert_eq!(min_window("Aa".to_string(), "a".to_string()), "a");
    }

    #[test]
    fn test_repeated_chars() {
        assert_eq!(min_window("aaabbbccc".to_string(), "abc".to_string()), "abbbc");
    }
}
