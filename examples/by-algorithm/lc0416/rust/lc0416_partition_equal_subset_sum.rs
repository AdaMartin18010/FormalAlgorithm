//! LeetCode 416. 分割等和子集 / Partition Equal Subset Sum
//!
//! 给你一个只包含正整数的非空数组 nums 。请你判断是否可以将这个数组分割成两个子集，
//! 使得两个子集的元素和相等。
//!
//! 题目链接: <https://leetcode.com/problems/partition-equal-subset-sum/>
//! 难度: Medium
//!
//! 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.5
//!
//! ## 形式化规约（0/1 背包判定）
//!
//! - **输入**: 正整数数组 $nums[0..n-1]$
//! - **输出**: $\exists S \subseteq [0,n-1]: \sum_{i \in S} nums[i] = \sum_{i \notin S} nums[i]$
//! - **前置条件**: $1 \leq n \leq 200$，$1 \leq nums[i] \leq 100$
//! - **后置条件**: 返回 true 当且仅当数组可被均分为两个和相等的子集
//!
//! ## 问题转化
//!
//! 设 $sum = \sum nums[i]$。若 $sum$ 为奇数，直接返回 false。
//! 否则问题转化为：**能否从 $nums$ 中选出一个子集，使其和为 $target = sum / 2$？**
//! 这正是 **0/1 背包** 的判定版本：物品重量 = $nums[i]$，价值无关紧要，背包容量 = $target$。
//!
//! ## 状态转移方程（布尔型 DP）
//!
//! $$ dp[i][w] = dp[i-1][w] \lor (w \geq nums[i] \land dp[i-1][w - nums[i]]) $$
//!
//! 其中 $dp[i][w]$ 表示前 $i$ 个物品能否凑出重量 $w$。
//!
//! ## 最优子结构引理
//!
//! **引理**: 前 $i$ 个物品能凑出重量 $w$，当且仅当：
//! - 前 $i-1$ 个物品已能凑出 $w$（不选第 $i$ 个），或
//! - $w \geq nums[i]$ 且前 $i-1$ 个物品能凑出 $w - nums[i]$（选第 $i$ 个）。
//!
//! **证明**: 前 $i$ 个物品的任意可行子集 $S$ 对第 $i$ 个物品只有两种选择：
//! - $i \notin S$: 则 $S$ 是前 $i-1$ 个物品凑出 $w$ 的子集。
//! - $i \in S$: 则 $S \setminus \{i\}$ 是前 $i-1$ 个物品凑出 $w - nums[i]$ 的子集。
//! 两种情况互斥且完备。$\square$

/// 判断数组是否能被分割成两个和相等的子集。
///
/// # 参数
///
/// * `nums` - 正整数数组
///
/// # 返回值
///
/// 若能均分则返回 true，否则返回 false。
///
/// # 复杂度分析
///
/// | 指标 | 值 | 说明 |
/// |------|-----|------|
/// | 时间复杂度 | $O(n \times target)$ | $target = sum / 2$ |
/// | 空间复杂度 | $O(target)$ | 一维布尔数组 + 逆序遍历 |
///
/// # 正确性证明
///
/// **定理**: 算法返回 true 当且仅当存在子集和为 $sum/2$。
///
/// **证明** (归纳法):
///
/// 设 $dp[w]$ 表示处理完当前物品后能否凑出重量 $w$。
///
/// - **基例**: $dp[0] = true$（空集和为 0），其余 $dp[w] = false$，正确。
/// - **归纳假设**: 处理完前 $i-1$ 个物品后，$dp[w]$ 正确反映前 $i-1$ 个物品能否凑出 $w$。
/// - **归纳步骤**: 处理第 $i$ 个物品时，逆序更新：
///   对每个 $w \geq nums[i]$，新 $dp[w] = $ 旧 $dp[w] \lor $ 旧 $dp[w - nums[i]]$。
///   由引理，这恰好是前 $i$ 个物品能否凑出 $w$ 的判定。
///   逆序遍历保证每个物品最多被选一次（0/1背包特性）。$\square$
pub fn can_partition(nums: Vec<i32>) -> bool {
    let sum: i32 = nums.iter().sum();
    if sum % 2 != 0 {
        return false;
    }
    let target = (sum / 2) as usize;
    let mut dp = vec![false; target + 1];
    dp[0] = true;

    for &num in &nums {
        let num = num as usize;
        // 逆序遍历：0/1 背包核心技巧，确保每个数字只用一次
        for w in (num..=target).rev() {
            dp[w] = dp[w] || dp[w - num];
        }
        // 提前终止
        if dp[target] {
            return true;
        }
    }

    dp[target]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert!(can_partition(vec![1, 5, 11, 5])); // [1,5,5] vs [11]
    }

    #[test]
    fn test_example_2() {
        assert!(!can_partition(vec![1, 2, 3, 5]));
    }

    #[test]
    fn test_single_element() {
        assert!(!can_partition(vec![1]));
    }

    #[test]
    fn test_two_equal() {
        assert!(can_partition(vec![2, 2]));
    }

    #[test]
    fn test_odd_sum() {
        assert!(can_partition(vec![1, 2, 3])); // sum = 6, target = 3, [1,2] vs [3]
        assert!(!can_partition(vec![1, 2, 4])); // sum = 7, odd
    }

    #[test]
    fn test_large_target() {
        assert!(can_partition(vec![3, 3, 3, 4, 5]));
    }

    #[test]
    fn test_all_ones() {
        assert!(can_partition(vec![1, 1, 1, 1, 1, 1, 1, 1])); // sum=8, target=4
    }

    #[test]
    fn test_impossible() {
        assert!(!can_partition(vec![100, 100, 100, 100, 100, 100, 100, 100, 1]));
    }
}
