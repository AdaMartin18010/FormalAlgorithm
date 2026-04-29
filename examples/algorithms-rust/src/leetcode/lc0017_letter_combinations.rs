//! LeetCode 17. 电话号码的字母组合
//!
//! 给定一个仅包含数字 2-9 的字符串，返回所有它能表示的字母组合。
//!
//! 对标: LeetCode 17 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md

/// 返回 digits 能表示的所有字母组合。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`digits` 仅由 `'2'`-`'9'` 组成，`0 <= digits.len() <= 4`。
/// - **后置条件 (Post)**：返回所有可能的字母组合向量；若 `digits` 为空，返回空向量；每个组合长度为 `digits.len()`。
///
/// # 回溯不变式
///
/// - `path` 为当前已选择的前缀字符串。
/// - `path.len()` 等于当前处理到的 `digits` 索引。
/// - `path` 中第 i 个字符来自 `digits[i]` 对应的字母集合。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(3^m × 4^n) — m 为对应 3 个字母的数字个数，n 为对应 4 个字母的数字个数。
/// - **空间复杂度**：O(digits.len()) — 递归栈深度。
///
/// # 证明要点
/// - 不遗漏：对每个数字，枚举其对应的所有字母，DFS 遍历笛卡尔积的全部元素。
/// - 不重复：`digits` 固定，每个位置独立选择，不同选择序列产生不同组合。
pub fn letter_combinations(digits: String) -> Vec<String> {
    if digits.is_empty() {
        return Vec::new();
    }

    let phone: std::collections::HashMap<char, &str> = [
        ('2', "abc"), ('3', "def"), ('4', "ghi"), ('5', "jkl"),
        ('6', "mno"), ('7', "pqrs"), ('8', "tuv"), ('9', "wxyz"),
    ].into_iter().collect();

    let digits: Vec<char> = digits.chars().collect();
    let n = digits.len();
    let mut result: Vec<String> = Vec::new();
    let mut path = String::with_capacity(n);

    fn backtrack(
        idx: usize,
        n: usize,
        digits: &[char],
        phone: &std::collections::HashMap<char, &str>,
        path: &mut String,
        result: &mut Vec<String>,
    ) {
        if idx == n {
            result.push(path.clone());
            return;
        }
        let chars = phone[&digits[idx]].chars();
        for ch in chars {
            path.push(ch);
            backtrack(idx + 1, n, digits, phone, path, result);
            path.pop();
        }
    }

    backtrack(0, n, &digits, &phone, &mut path, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let result = letter_combinations("23".to_string());
        assert_eq!(result.len(), 9);
        let expected: std::collections::HashSet<String> = [
            "ad", "ae", "af", "bd", "be", "bf", "cd", "ce", "cf",
        ].iter().map(|s| s.to_string()).collect();
        let actual: std::collections::HashSet<String> = result.into_iter().collect();
        assert_eq!(actual, expected);
    }

    #[test]
    fn test_empty_digits() {
        assert!(letter_combinations("".to_string()).is_empty());
    }

    #[test]
    fn test_single_digit() {
        assert_eq!(
            letter_combinations("2".to_string()),
            vec!["a", "b", "c"]
        );
    }

    #[test]
    fn test_79_combinations() {
        assert_eq!(letter_combinations("79".to_string()).len(), 16);
    }
}
