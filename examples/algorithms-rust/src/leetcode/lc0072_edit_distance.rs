/// LeetCode 72. Edit Distance
/// https://leetcode.com/problems/edit-distance/
///
/// Problem: Given two strings word1 and word2, return the minimum number of operations
/// required to convert word1 to word2. Operations: insert, delete, replace.
///
/// Formal specification:
/// - Pre: word1, word2 are ASCII/Unicode strings
/// - Post: result = min ops to transform word1 → word2
///
/// Algorithm: Classic DP with optimal substructure.
/// dp[i][j] = min edit distance between word1[0..i) and word2[0..j).
///
/// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
/// Lean proof: examples/lean_proofs/leetcode/lc0072_edit_distance.lean

pub fn min_distance(word1: String, word2: String) -> i32 {
    let m = word1.len();
    let n = word2.len();
    let w1: Vec<char> = word1.chars().collect();
    let w2: Vec<char> = word2.chars().collect();

    // dp[j] represents edit distance for word1[0..i) vs word2[0..j)
    let mut dp = vec![0; n + 1];

    // Base case: transform empty word1 to word2[0..j) requires j insertions
    for j in 0..=n {
        dp[j] = j as i32;
    }

    for i in 1..=m {
        let mut prev = dp[0]; // dp[i-1][0]
        dp[0] = i as i32;     // transform word1[0..i) to empty word2: i deletions

        for j in 1..=n {
            let temp = dp[j];
            if w1[i - 1] == w2[j - 1] {
                // Characters match: no operation needed
                dp[j] = prev;
            } else {
                // Choose minimum among delete, insert, substitute
                let delete = dp[j] + 1;      // delete w1[i-1]
                let insert = dp[j - 1] + 1;  // insert w2[j-1]
                let substitute = prev + 1;    // replace w1[i-1] with w2[j-1]
                dp[j] = delete.min(insert).min(substitute);
            }
            prev = temp;
        }
    }

    dp[n]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(min_distance("horse".to_string(), "ros".to_string()), 3);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(
            min_distance("intention".to_string(), "execution".to_string()),
            5
        );
    }

    #[test]
    fn test_empty_strings() {
        assert_eq!(min_distance("".to_string(), "".to_string()), 0);
        assert_eq!(min_distance("abc".to_string(), "".to_string()), 3);
        assert_eq!(min_distance("".to_string(), "abc".to_string()), 3);
    }

    #[test]
    fn test_same_string() {
        assert_eq!(min_distance("abc".to_string(), "abc".to_string()), 0);
    }

    #[test]
    fn test_single_char() {
        assert_eq!(min_distance("a".to_string(), "b".to_string()), 1);
    }
}
