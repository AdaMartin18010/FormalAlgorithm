//! 后缀自动机 (Suffix Automaton, SAM)
//!
//! 一种紧凑的字符串后缀数据结构，可以高效地处理和查询子串相关信息。
//!
//! ## 核心思想
//! - 每个状态代表一类结束位置集合（endpos）相同的子串
//! - 转移函数：从状态 p 通过字符 c 转移到状态 q
//! - Link（后缀链接）：指向当前状态的最长真后缀对应的状态
//! - len：该状态表示的最长子串长度
//!
//! ## 性质
//! - 状态数不超过 2n-1（n为字符串长度）
//! - 转移数不超过 3n-4
//! - 后缀链接构成一棵以初始状态为根的树
//!
//! ## 适用问题
//! - 子串出现次数查询
//! - 不同子串个数统计
//! - 最长公共子串
//! - 第 k 小子串
//! - 最长重复子串
//!
//! ## 复杂度分析
//! - 构建: O(n) 时间和空间
//! - 查询: O(|pattern|)
//!
//! 对标: 高级字符串算法

use std::collections::HashMap;

/// 后缀自动机状态
#[derive(Clone, Debug)]
pub struct State {
    /// 转移函数: 字符 -> 目标状态
    pub next: HashMap<char, usize>,
    /// 后缀链接
    pub link: Option<usize>,
    /// 该状态表示的最长子串长度
    pub len: usize,
    /// 结束位置数量（出现次数）
    pub occ: usize,
    /// 是否为克隆状态
    pub is_clone: bool,
}

impl State {
    /// 创建新状态
    pub fn new(len: usize) -> Self {
        State {
            next: HashMap::new(),
            link: None,
            len,
            occ: 0,
            is_clone: false,
        }
    }
}

/// 后缀自动机
#[derive(Clone, Debug)]
pub struct SuffixAutomaton {
    /// 所有状态
    pub states: Vec<State>,
    /// 初始状态（空串对应的状态）
    pub initial: usize,
    /// 最后添加字符对应的状态
    pub last: usize,
}

impl SuffixAutomaton {
    /// 从字符串构建后缀自动机
    ///
    /// # 参数
    /// - `s`: 输入字符串
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn new(s: &str) -> Self {
        let mut sam = SuffixAutomaton {
            states: vec![State::new(0)],
            initial: 0,
            last: 0,
        };

        for ch in s.chars() {
            sam.extend(ch);
        }

        sam
    }

    /// 扩展自动机（添加一个字符）
    ///
    /// # 参数
    /// - `c`: 要添加的字符
    ///
    /// # 复杂度
    /// - 摊还时间: O(1)
    fn extend(&mut self, c: char) {
        let cur = self.states.len();
        self.states.push(State::new(self.states[self.last].len + 1));
        self.states[cur].occ = 1; // 新状态代表的实际出现位置

        let mut p = Some(self.last);

        // 沿着后缀链接寻找有 c 转移的状态
        while let Some(pi) = p {
            if self.states[pi].next.contains_key(&c) {
                break;
            }
            self.states[pi].next.insert(c, cur);
            p = self.states[pi].link;
        }

        if let Some(pi) = p {
            let q = self.states[pi].next[&c];
            if self.states[pi].len + 1 == self.states[q].len {
                // 直接设置后缀链接
                self.states[cur].link = Some(q);
            } else {
                // 需要分裂状态
                let clone = self.states.len();
                let mut clone_state = State::new(self.states[pi].len + 1);
                clone_state.next = self.states[q].next.clone();
                clone_state.link = self.states[q].link;
                clone_state.occ = 0; // 克隆状态的 occ 为 0
                clone_state.is_clone = true;
                self.states.push(clone_state);

                // 更新转移和后缀链接
                while let Some(pj) = p {
                    if self.states[pj].next.get(&c) != Some(&q) {
                        break;
                    }
                    self.states[pj].next.insert(c, clone);
                    p = self.states[pj].link;
                }

                self.states[q].link = Some(clone);
                self.states[cur].link = Some(clone);
            }
        } else {
            // 没有找到，链接到初始状态
            self.states[cur].link = Some(self.initial);
        }

        self.last = cur;
    }

    /// 计算每个状态的出现次数（拓扑排序后）
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn calculate_occurrences(&mut self) {
        let max_len = self.states.iter().map(|s| s.len).max().unwrap_or(0);
        let mut cnt = vec![0usize; max_len + 1];

        // 计数排序
        for state in &self.states {
            cnt[state.len] += 1;
        }
        for i in 1..=max_len {
            cnt[i] += cnt[i - 1];
        }

        let mut order = vec![0usize; self.states.len()];
        for i in (0..self.states.len()).rev() {
            cnt[self.states[i].len] -= 1;
            order[cnt[self.states[i].len]] = i;
        }

        // 逆序传播出现次数
        for i in (1..order.len()).rev() {
            let state_idx = order[i];
            if let Some(link) = self.states[state_idx].link {
                self.states[link].occ += self.states[state_idx].occ;
            }
        }
    }

    /// 查询子串出现次数
    ///
    /// # 参数
    /// - `pattern`: 要查询的子串
    ///
    /// # 返回值
    /// 子串出现次数，如果不存在则返回 0
    ///
    /// # 复杂度
    /// - 时间: O(|pattern|)
    pub fn count_occurrences(&self, pattern: &str) -> usize {
        let mut state_idx = self.initial;

        for ch in pattern.chars() {
            match self.states[state_idx].next.get(&ch) {
                Some(&next_idx) => state_idx = next_idx,
                None => return 0,
            }
        }

        self.states[state_idx].occ
    }

    /// 检查子串是否存在
    ///
    /// # 复杂度
    /// - 时间: O(|pattern|)
    pub fn contains(&self, pattern: &str) -> bool {
        let mut state_idx = self.initial;

        for ch in pattern.chars() {
            match self.states[state_idx].next.get(&ch) {
                Some(&next_idx) => state_idx = next_idx,
                None => return false,
            }
        }

        true
    }

    /// 计算不同子串个数
    ///
    /// # 返回值
    /// 原字符串的不同子串数量
    ///
    /// # 复杂度
    /// - 时间: O(n)
    pub fn count_distinct_substrings(&self) -> usize {
        let mut count = 0usize;

        for i in 1..self.states.len() {
            let state = &self.states[i];
            let parent_len = state.link.map(|l| self.states[l].len).unwrap_or(0);
            count += state.len - parent_len;
        }

        count
    }

    /// 获取最长重复子串长度
    ///
    /// # 返回值
    /// 至少出现两次的最长子串的长度
    ///
    /// # 复杂度
    /// - 时间: O(n)
    pub fn longest_repeated_substring(&self) -> usize {
        let mut max_len = 0;

        for i in 1..self.states.len() {
            if self.states[i].occ >= 2 {
                max_len = max_len.max(self.states[i].len);
            }
        }

        max_len
    }

    /// 查找第 k 小子串（按字典序）
    ///
    /// # 参数
    /// - `k`: 第 k 小（从1开始计数）
    ///
    /// # 返回值
    /// 第 k 小的子串，如果不存在则返回 None
    ///
    /// # 复杂度
    /// - 时间: O(|answer|)
    pub fn kth_smallest_substring(&self, mut k: usize) -> Option<String> {
        // 检查 k 是否有效
        let total = self.count_distinct_substrings();
        if k == 0 || k > total {
            return None;
        }

        // 先计算每个状态能到达多少个子串（不包括空串）
        let mut dp = vec![0usize; self.states.len()];
        self.calc_dp(self.initial, &mut dp);

        let mut result = String::new();
        let mut state_idx = self.initial;

        loop {
            // 按字典序遍历转移
            let mut chars: Vec<char> = self.states[state_idx].next.keys().cloned().collect();
            chars.sort_unstable();

            for ch in chars {
                let next_idx = self.states[state_idx].next[&ch];
                let count = dp[next_idx];
                if k > count {
                    k -= count;
                } else {
                    result.push(ch);
                    state_idx = next_idx;
                    k -= 1; // 减去当前子串本身
                    if k == 0 {
                        return Some(result);
                    }
                    break;
                }
            }
        }
    }

    /// 计算从某个状态出发能到达多少个子串（包括空串）
    fn calc_dp(&self, state_idx: usize, dp: &mut [usize]) -> usize {
        if dp[state_idx] > 0 {
            return dp[state_idx];
        }

        let mut count = 1; // 空串
        for &next_idx in self.states[state_idx].next.values() {
            count += self.calc_dp(next_idx, dp);
        }

        dp[state_idx] = count;
        count
    }

    /// 获取所有状态信息（调试用）
    pub fn get_states_info(&self) -> Vec<(usize, usize, Option<usize>, usize)> {
        self.states
            .iter()
            .enumerate()
            .map(|(i, s)| (i, s.len, s.link, s.occ))
            .collect()
    }

    /// 获取状态数
    pub fn state_count(&self) -> usize {
        self.states.len()
    }
}

/// 两个字符串的最长公共子串
///
/// # 参数
/// - `s1`, `s2`: 两个字符串
///
/// # 返回值
/// 最长公共子串及其长度
///
/// # 复杂度
/// - 时间: O(|s1| + |s2|)
/// - 空间: O(|s1|)
pub fn longest_common_substring(s1: &str, s2: &str) -> (String, usize) {
    let sam = SuffixAutomaton::new(s1);

    let mut state_idx = sam.initial;
    let mut current_len = 0;
    let mut best_len = 0;
    let mut best_end_pos = 0;

    for (i, ch) in s2.chars().enumerate() {
        if let Some(&next_idx) = sam.states[state_idx].next.get(&ch) {
            state_idx = next_idx;
            current_len += 1;
        } else {
            // 沿着后缀链接寻找有该转移的状态
            while state_idx != sam.initial && !sam.states[state_idx].next.contains_key(&ch) {
                state_idx = sam.states[state_idx].link.unwrap_or(sam.initial);
            }

            if let Some(&next_idx) = sam.states[state_idx].next.get(&ch) {
                current_len = sam.states[state_idx].len + 1;
                state_idx = next_idx;
            } else {
                state_idx = sam.initial;
                current_len = 0;
            }
        }

        if current_len > best_len {
            best_len = current_len;
            best_end_pos = i;
        }
    }

    if best_len == 0 {
        return (String::new(), 0);
    }

    let start = best_end_pos + 1 - best_len;
    let lcs: String = s2.chars().skip(start).take(best_len).collect();
    (lcs, best_len)
}

/// 多个字符串的最长公共子串
///
/// # 复杂度
/// - 时间: O(total_length × number_of_strings)
/// - 空间: O(max_string_length)
pub fn longest_common_substring_multiple(strings: &[String]) -> (String, usize) {
    if strings.is_empty() {
        return (String::new(), 0);
    }
    if strings.len() == 1 {
        return (strings[0].clone(), strings[0].len());
    }

    // 使用二分查找 + 哈希的方法
    let min_len = strings.iter().map(|s| s.len()).min().unwrap_or(0);

    fn has_common_substring_of_len(strings: &[String], len: usize) -> Option<String> {
        if len == 0 {
            return Some(String::new());
        }

        use std::collections::HashSet;

        // 获取第一个字符串的所有长度为 len 的子串
        let mut substrings: HashSet<String> = HashSet::new();
        let first = &strings[0];
        for i in 0..=first.len() - len {
            substrings.insert(first[i..i + len].to_string());
        }

        // 对其他字符串取交集
        for s in &strings[1..] {
            let mut new_set: HashSet<String> = HashSet::new();
            for i in 0..=s.len() - len {
                let sub = s[i..i + len].to_string();
                if substrings.contains(&sub) {
                    new_set.insert(sub);
                }
            }
            substrings = new_set;
            if substrings.is_empty() {
                return None;
            }
        }

        substrings.into_iter().next()
    }

    // 二分查找最长公共子串长度
    let mut left = 0usize;
    let mut right = min_len;
    let mut result = String::new();

    while left <= right {
        let mid = (left + right) / 2;
        if let Some(common) = has_common_substring_of_len(strings, mid) {
            result = common;
            left = mid + 1;
        } else {
            if mid == 0 {
                break;
            }
            right = mid - 1;
        }
    }

    let final_len = result.len();
    (result, final_len)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_suffix_automaton() {
        let mut sam = SuffixAutomaton::new("abab");
        sam.calculate_occurrences();

        // 测试出现次数
        assert_eq!(sam.count_occurrences("a"), 2);
        assert_eq!(sam.count_occurrences("b"), 2);
        assert_eq!(sam.count_occurrences("ab"), 2);
        assert_eq!(sam.count_occurrences("ba"), 1);
        assert_eq!(sam.count_occurrences("aba"), 1);
        assert_eq!(sam.count_occurrences("bab"), 1);
        assert_eq!(sam.count_occurrences("abab"), 1);
        assert_eq!(sam.count_occurrences("abc"), 0);

        // 测试存在性
        assert!(sam.contains("ab"));
        assert!(!sam.contains("abc"));
    }

    #[test]
    fn test_distinct_substrings() {
        // "abab" 的不同子串:
        // "a", "b", "ab", "ba", "aba", "bab", "abab"
        let sam = SuffixAutomaton::new("abab");
        assert_eq!(sam.count_distinct_substrings(), 7);

        // "aaaa" 的不同子串:
        // "a", "aa", "aaa", "aaaa"
        let sam2 = SuffixAutomaton::new("aaaa");
        assert_eq!(sam2.count_distinct_substrings(), 4);

        // "abcd" 的不同子串: 4 + 3 + 2 + 1 = 10
        let sam3 = SuffixAutomaton::new("abcd");
        assert_eq!(sam3.count_distinct_substrings(), 10);
    }

    #[test]
    fn test_longest_repeated_substring() {
        // "abab" 的最长重复子串是 "ab"，出现2次
        let mut sam = SuffixAutomaton::new("abab");
        sam.calculate_occurrences();
        assert_eq!(sam.longest_repeated_substring(), 2);

        // "abcd" 没有重复子串
        let mut sam2 = SuffixAutomaton::new("abcd");
        sam2.calculate_occurrences();
        assert_eq!(sam2.longest_repeated_substring(), 0);

        // "aaaa" 的最长重复子串是 "aaa"，出现2次
        let mut sam3 = SuffixAutomaton::new("aaaa");
        sam3.calculate_occurrences();
        assert_eq!(sam3.longest_repeated_substring(), 3);
    }

    #[test]
    fn test_kth_smallest_substring() {
        // "ababa" 的所有子串按字典序排列:
        // 去重后: "a", "ab", "aba", "abab", "ababa", "b", "ba", "bab", "baba" (共9个)
        let sam = SuffixAutomaton::new("ababa");

        // 基本测试：确保能返回正确的子串数量
        assert_eq!(sam.count_distinct_substrings(), 9);

        // 第 k 小查询的基本测试
        assert_eq!(sam.kth_smallest_substring(1), Some("a".to_string()));
        assert_eq!(sam.kth_smallest_substring(9), Some("baba".to_string()));
        assert_eq!(sam.kth_smallest_substring(10), None);
        assert_eq!(sam.kth_smallest_substring(0), None);
    }

    #[test]
    fn test_longest_common_substring() {
        // "abcdef" 和 "zbcdfg" 的最长公共子串是 "bcd"
        let (lcs, len) = longest_common_substring("abcdef", "zbcdfg");
        assert_eq!(lcs, "bcd");
        assert_eq!(len, 3);

        // 无公共子串
        let (lcs2, len2) = longest_common_substring("abc", "def");
        assert_eq!(lcs2, "");
        assert_eq!(len2, 0);

        // 完全相同的字符串
        let (lcs3, len3) = longest_common_substring("abcd", "abcd");
        assert_eq!(lcs3, "abcd");
        assert_eq!(len3, 4);
    }

    #[test]
    fn test_longest_common_substring_multiple() {
        let strings = vec![
            "abcdef".to_string(),
            "zbcdfg".to_string(),
            "xbcdyz".to_string(),
        ];

        let (lcs, len) = longest_common_substring_multiple(&strings);
        assert_eq!(lcs, "bcd");
        assert_eq!(len, 3);
    }

    #[test]
    fn test_empty_string() {
        let sam = SuffixAutomaton::new("");
        assert_eq!(sam.count_distinct_substrings(), 0);
        assert_eq!(sam.state_count(), 1); // 只有初始状态
    }

    #[test]
    fn test_single_char() {
        let mut sam = SuffixAutomaton::new("a");
        sam.calculate_occurrences();

        assert_eq!(sam.count_occurrences("a"), 1);
        assert_eq!(sam.count_distinct_substrings(), 1);
        assert_eq!(sam.longest_repeated_substring(), 0);
    }

    #[test]
    fn test_state_count() {
        // SAM 的状态数不超过 2n-1
        let sam = SuffixAutomaton::new("abcd");
        assert!(sam.state_count() <= 2 * "abcd".len());

        let sam2 = SuffixAutomaton::new("aaaa");
        assert!(sam2.state_count() <= 2 * "aaaa".len());
    }

    #[test]
    fn test_complex_occurrences() {
        let mut sam = SuffixAutomaton::new("banana");
        sam.calculate_occurrences();

        // "an" 出现2次: "b**an**ana", "ban**an**a"
        assert_eq!(sam.count_occurrences("an"), 2);

        // "na" 出现2次
        assert_eq!(sam.count_occurrences("na"), 2);

        // "a" 出现3次
        assert_eq!(sam.count_occurrences("a"), 3);
    }
}
