/// LeetCode 96. Unique Binary Search Trees
///
/// Given an integer `n`, return the number of structurally unique BST's
/// (binary search trees) which has exactly `n` nodes of unique values from 1 to n.
///
/// # Approach
/// Catalan number DP. For each possible root value `i` (1..n),
/// left subtree has `i-1` nodes and right subtree has `n-i` nodes.
/// dp[n] = Σ dp[i-1] * dp[n-i] for i = 1..n.
///
/// # Correctness Proof
/// By induction on n. Base case n=0: one empty tree (dp[0]=1).
/// For n nodes, choose root i. Left subtree values are 1..i-1 (dp[i-1] shapes),
/// right subtree values are i+1..n (dp[n-i] shapes).
/// By multiplication principle, root i contributes dp[i-1]*dp[n-i] trees.
/// Summing over all i gives dp[n].
///
/// # Complexity
/// - Time complexity: O(n²)
/// - Space complexity: O(n)

pub struct Solution;

impl Solution {
    pub fn num_trees(n: i32) -> i32 {
        let n = n as usize;
        let mut dp = vec![0; n + 1];
        dp[0] = 1;

        for nodes in 1..=n {
            for root in 1..=nodes {
                dp[nodes] += dp[root - 1] * dp[nodes - root];
            }
        }

        dp[n]
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(Solution::num_trees(3), 5);
    }

    #[test]
    fn test_example_2() {
        assert_eq!(Solution::num_trees(1), 1);
    }

    #[test]
    fn test_zero() {
        assert_eq!(Solution::num_trees(0), 1);
    }

    #[test]
    fn test_catalan_numbers() {
        // C0=1, C1=1, C2=2, C3=5, C4=14, C5=42
        assert_eq!(Solution::num_trees(2), 2);
        assert_eq!(Solution::num_trees(4), 14);
        assert_eq!(Solution::num_trees(5), 42);
    }
}
