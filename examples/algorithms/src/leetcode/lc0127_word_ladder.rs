//! LeetCode 127. 单词接龙
//!
//! 给定两个单词 beginWord 和 endWord，以及一个字典 wordList，
//! 返回从 beginWord 到 endWord 的最短转换序列的长度。每次转换只能改变一个字母。
//!
//! 对标: LeetCode 127 / docs/13-LeetCode算法面试专题/02-算法范式专题/10-BFS与图搜索.md

use std::collections::{HashSet, VecDeque};

/// 返回从 begin_word 到 end_word 的最短转换序列长度。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`begin_word`, `end_word` 长度相同，由小写英文字母组成；
///   `word_list` 中单词长度与 `begin_word` 相同。
/// - **后置条件 (Post)**：若存在转换序列，返回序列长度（包含两端）；若不存在，返回 0。
///
/// # BFS 层级不变式
///
/// BFS 第 d 层恰好包含距 `begin_word` 最短转换距离为 d 的所有单词。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(N × L²) — N 为 `word_list` 长度，L 为单词长度。
/// - **空间复杂度**：O(N × L) — 访问标记集合与队列。
///
/// # 证明要点
/// - 正确性：BFS 按层扩展，第一次到达 `end_word` 时即为最短路径（无权图最短路径定理）。
/// - 双向 BFS 优化：从两端同时 BFS，每次扩展较小的一侧，将搜索空间从 O(b^d) 降为 O(b^(d/2))。
pub fn ladder_length(begin_word: String, end_word: String, word_list: Vec<String>) -> i32 {
    let word_set: HashSet<String> = word_list.into_iter().collect();
    if !word_set.contains(&end_word) {
        return 0;
    }
    if begin_word == end_word {
        return 1;
    }

    let mut begin_visited = HashSet::new();
    let mut end_visited = HashSet::new();
    begin_visited.insert(begin_word.clone());
    end_visited.insert(end_word.clone());

    let mut begin_queue = VecDeque::new();
    let mut end_queue = VecDeque::new();
    begin_queue.push_back(begin_word);
    end_queue.push_back(end_word);

    let mut length = 1;

    while !begin_queue.is_empty() && !end_queue.is_empty() {
        // 扩展较小的一侧
        if begin_queue.len() > end_queue.len() {
            std::mem::swap(&mut begin_queue, &mut end_queue);
            std::mem::swap(&mut begin_visited, &mut end_visited);
        }

        length += 1;
        let level_size = begin_queue.len();
        for _ in 0..level_size {
            let word = begin_queue.pop_front().unwrap();
            let mut chars: Vec<char> = word.chars().collect();
            for i in 0..chars.len() {
                let original = chars[i];
                for c in 'a'..='z' {
                    if c == original {
                        continue;
                    }
                    chars[i] = c;
                    let new_word: String = chars.iter().collect();
                    if !word_set.contains(&new_word) {
                        continue;
                    }
                    if begin_visited.contains(&new_word) {
                        continue;
                    }
                    if end_visited.contains(&new_word) {
                        return length;
                    }
                    begin_visited.insert(new_word.clone());
                    begin_queue.push_back(new_word);
                }
                chars[i] = original;
            }
        }
    }

    0
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let word_list = vec![
            "hot".to_string(), "dot".to_string(), "dog".to_string(),
            "lot".to_string(), "log".to_string(), "cog".to_string(),
        ];
        assert_eq!(ladder_length("hit".to_string(), "cog".to_string(), word_list), 5);
    }

    #[test]
    fn test_leetcode_example_2() {
        let word_list = vec![
            "hot".to_string(), "dot".to_string(), "dog".to_string(),
            "lot".to_string(), "log".to_string(),
        ];
        assert_eq!(ladder_length("hit".to_string(), "cog".to_string(), word_list), 0);
    }

    #[test]
    fn test_same_word() {
        assert_eq!(ladder_length("a".to_string(), "a".to_string(), vec![]), 1);
    }

    #[test]
    fn test_single_step() {
        assert_eq!(ladder_length("a".to_string(), "b".to_string(), vec!["b".to_string()]), 2);
    }
}
