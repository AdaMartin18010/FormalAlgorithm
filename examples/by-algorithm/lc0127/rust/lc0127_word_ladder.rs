//! LeetCode 127. Word Ladder
//! 链接: https://leetcode.com/problems/word-ladder/
//! 难度: Hard
//!
//! 算法: 双向 BFS
//! 时间复杂度: O(N * L^2)，N=wordList 大小，L=单词长度
//! 空间复杂度: O(N)

use std::collections::{HashMap, HashSet, VecDeque};

pub struct Solution;

impl Solution {
    /// 返回从 begin_word 到 end_word 的最短转换序列长度。
    pub fn ladder_length(begin_word: String, end_word: String, word_list: Vec<String>) -> i32 {
        let word_set: HashSet<String> = word_list.into_iter().collect();
        if !word_set.contains(&end_word) {
            return 0;
        }

        if begin_word == end_word {
            return 1;
        }

        // 双向 BFS
        let mut begin_visited: HashMap<String, i32> = HashMap::new();
        let mut end_visited: HashMap<String, i32> = HashMap::new();
        let mut begin_queue: VecDeque<String> = VecDeque::new();
        let mut end_queue: VecDeque<String> = VecDeque::new();

        begin_visited.insert(begin_word.clone(), 1);
        end_visited.insert(end_word.clone(), 1);
        begin_queue.push_back(begin_word);
        end_queue.push_back(end_word);

        while !begin_queue.is_empty() && !end_queue.is_empty() {
            // 从较小的一侧扩展
            if begin_queue.len() > end_queue.len() {
                std::mem::swap(&mut begin_queue, &mut end_queue);
                std::mem::swap(&mut begin_visited, &mut end_visited);
            }

            let level_size = begin_queue.len();
            for _ in 0..level_size {
                let word = begin_queue.pop_front().unwrap();
                let current_len = *begin_visited.get(&word).unwrap();
                let word_chars: Vec<char> = word.chars().collect();

                for i in 0..word_chars.len() {
                    for c in 'a'..='z' {
                        if c == word_chars[i] {
                            continue;
                        }
                        let mut next_chars = word_chars.clone();
                        next_chars[i] = c;
                        let next_word: String = next_chars.into_iter().collect();

                        if !word_set.contains(&next_word) {
                            continue;
                        }

                        // 检查是否在另一侧已访问
                        if let Some(&end_len) = end_visited.get(&next_word) {
                            return current_len + end_len;
                        }

                        if !begin_visited.contains_key(&next_word) {
                            begin_visited.insert(next_word.clone(), current_len + 1);
                            begin_queue.push_back(next_word);
                        }
                    }
                }
            }
        }

        0
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_ladder_length_basic() {
        let begin = "hit".to_string();
        let end = "cog".to_string();
        let word_list = vec![
            "hot".to_string(),
            "dot".to_string(),
            "dog".to_string(),
            "lot".to_string(),
            "log".to_string(),
            "cog".to_string(),
        ];
        assert_eq!(Solution::ladder_length(begin, end, word_list), 5);
    }

    #[test]
    fn test_ladder_length_no_path() {
        let begin = "hit".to_string();
        let end = "cog".to_string();
        let word_list = vec![
            "hot".to_string(),
            "dot".to_string(),
            "dog".to_string(),
            "lot".to_string(),
            "log".to_string(),
        ];
        assert_eq!(Solution::ladder_length(begin, end, word_list), 0);
    }
}
