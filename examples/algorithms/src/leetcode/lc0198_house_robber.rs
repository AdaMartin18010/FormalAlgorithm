/// LeetCode 198. House Robber
/// https://leetcode.com/problems/house-robber/
///
/// Problem: Given an integer array nums representing money in each house,
/// return the maximum amount you can rob without alerting police.
/// Cannot rob two adjacent houses.
///
/// Formal specification:
/// - Pre: nums.len() >= 0
/// - Post: result = max sum of non-adjacent elements
///
/// Algorithm: DP with optimal substructure.
/// dp[i] = max money from houses[0..i].
/// Recurrence: dp[i] = max(dp[i-1], dp[i-2] + nums[i]).
///
/// Reference: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md
/// Lean proof: examples/lean_proofs/leetcode/lc0198_house_robber.lean

pub fn rob(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    if n == 0 {
        return 0;
    }
    if n == 1 {
        return nums[0];
    }

    let mut prev2 = nums[0];
    let mut prev1 = nums[0].max(nums[1]);

    for i in 2..n {
        let curr = prev1.max(prev2 + nums[i]);
        prev2 = prev1;
        prev1 = curr;
    }

    prev1
}

// Space-optimized version using O(1) extra space
pub fn rob_optimized(nums: Vec<i32>) -> i32 {
    let (mut rob_prev, mut not_rob_prev) = (0, 0);

    for &money in nums.iter() {
        let rob_curr = not_rob_prev + money; // rob current: previous must not be robbed
        let not_rob_curr = rob_prev.max(not_rob_prev); // not rob current: take max of previous states
        rob_prev = rob_curr;
        not_rob_prev = not_rob_curr;
    }

    rob_prev.max(not_rob_prev)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(rob(vec![1, 2, 3, 1]), 4); // 1 + 3
    }

    #[test]
    fn test_example_2() {
        assert_eq!(rob(vec![2, 7, 9, 3, 1]), 12); // 2 + 9 + 1
    }

    #[test]
    fn test_empty() {
        assert_eq!(rob(vec![]), 0);
    }

    #[test]
    fn test_single() {
        assert_eq!(rob(vec![5]), 5);
    }

    #[test]
    fn test_two() {
        assert_eq!(rob(vec![3, 5]), 5);
    }

    #[test]
    fn test_optimized() {
        assert_eq!(rob_optimized(vec![1, 2, 3, 1]), 4);
        assert_eq!(rob_optimized(vec![2, 7, 9, 3, 1]), 12);
    }
}
