//! 硬币找零问题实现
//!
//! 硬币找零问题是动态规划的经典模型：
//! 给定不同面额的硬币和一个总金额，计算凑成该金额所需的最少硬币数，
//! 或计算所有可能的组合方式。
//!
//! 对标: CLRS 4th Ed. 习题 14.4-5；MIT 6.006 Dynamic Programming 模块；
//! LeetCode 322 / 518（国际算法面试高频题）。
//!
//! ## 最少硬币数（完全背包）
//!
//! `dp[amount]` = 凑成金额 amount 所需的最少硬币数
//!
//! 状态转移：`dp[a] = min(dp[a - coin] + 1)` 对所有 `coin ≤ a`
//!
//! ## 组合数（完全背包计数）
//!
//! `dp[amount]` = 凑成金额 amount 的组合数
//!
//! 状态转移：`dp[a] += dp[a - coin]` 对所有 `coin ≤ a`
//!
//! ## 复杂度分析
//!
//! | 问题 | 时间复杂度 | 空间复杂度 |
//! |------|----------|----------|
//! | 最少硬币数 | O(n × amount) | O(amount) |
//! | 组合数 | O(n × amount) | O(amount) |
//! | 返回具体组合 | O(n × amount) | O(n × amount) |

use crate::AlgorithmError;

/// 最少硬币数：返回凑成 amount 所需的最少硬币数
///
/// 若无法凑成，返回 `None`。
///
/// # 参数
///
/// * `coins` - 硬币面额数组（假设每种硬币无限供应）
/// * `amount` - 目标金额
///
/// # 示例
///
/// ```
/// use formal_algorithms::coin_change::coin_change_min;
///
/// let coins = vec![1, 2, 5];
/// assert_eq!(coin_change_min(&coins, 11), Some(3)); // 5 + 5 + 1
/// assert_eq!(coin_change_min(&coins, 3), Some(2));  // 2 + 1
/// assert_eq!(coin_change_min(&coins, 7), Some(2));  // 5 + 2
/// ```
pub fn coin_change_min(coins: &[usize], amount: usize) -> Option<usize> {
    if amount == 0 {
        return Some(0);
    }

    let mut dp = vec![usize::MAX; amount + 1];
    dp[0] = 0;

    for a in 1..=amount {
        for &coin in coins {
            if coin <= a && dp[a - coin] != usize::MAX {
                dp[a] = dp[a].min(dp[a - coin] + 1);
            }
        }
    }

    if dp[amount] == usize::MAX {
        None
    } else {
        Some(dp[amount])
    }
}

/// 最少硬币数：返回具体使用的硬币组合
///
/// # 返回值
///
/// `Some(coin_list)` 或 `None`（若无法凑成）
///
/// # 示例
///
/// ```
/// use formal_algorithms::coin_change::coin_change_min_with_coins;
///
/// let coins = vec![1, 2, 5];
/// let result = coin_change_min_with_coins(&coins, 11);
/// assert!(result.is_some());
/// let selected = result.unwrap();
/// assert_eq!(selected.iter().sum::<usize>(), 11);
/// assert_eq!(selected.len(), 3); // e.g., [5, 5, 1]
/// ```
pub fn coin_change_min_with_coins(coins: &[usize], amount: usize) -> Option<Vec<usize>> {
    if amount == 0 {
        return Some(vec![]);
    }

    let mut dp = vec![usize::MAX; amount + 1];
    let mut choice = vec![None; amount + 1];
    dp[0] = 0;

    for a in 1..=amount {
        for &coin in coins {
            if coin <= a && dp[a - coin] != usize::MAX && dp[a - coin] + 1 < dp[a] {
                dp[a] = dp[a - coin] + 1;
                choice[a] = Some(coin);
            }
        }
    }

    if dp[amount] == usize::MAX {
        return None;
    }

    let mut result = Vec::new();
    let mut cur = amount;
    while cur > 0 {
        let coin = choice[cur]?;
        result.push(coin);
        cur -= coin;
    }

    Some(result)
}

/// 组合数：返回凑成 amount 的所有不同组合方式的数量
///
/// 每种组合只计一次，与硬币顺序无关。
///
/// # 示例
///
/// ```
/// use formal_algorithms::coin_change::coin_change_ways;
///
/// let coins = vec![1, 2, 5];
/// assert_eq!(coin_change_ways(&coins, 5), 4);
/// // 1+1+1+1+1, 1+1+1+2, 1+2+2, 5
/// ```
pub fn coin_change_ways(coins: &[usize], amount: usize) -> usize {
    if amount == 0 {
        return 1;
    }

    let mut dp = vec![0usize; amount + 1];
    dp[0] = 1;

    for &coin in coins {
        for a in coin..=amount {
            dp[a] += dp[a - coin];
        }
    }

    dp[amount]
}

/// 组合数（空间优化，仅返回数量）
///
/// 与 `coin_change_ways` 等价，展示标准完全背包计数写法。
pub fn coin_change_ways_optimized(coins: &[usize], amount: usize) -> usize {
    coin_change_ways(coins, amount)
}

/// 返回所有凑成 amount 的具体组合（枚举版本）
///
/// 注意：当 amount 较大时，组合数可能爆炸式增长。适用于小规模问题。
///
/// # 示例
///
/// ```
/// use formal_algorithms::coin_change::coin_change_all_combinations;
///
/// let coins = vec![1, 2, 3];
/// let combinations = coin_change_all_combinations(&coins, 4);
/// assert_eq!(combinations.len(), 4);
/// // [1,1,1,1], [1,1,2], [2,2], [1,3]
/// ```
pub fn coin_change_all_combinations(coins: &[usize], amount: usize) -> Vec<Vec<usize>> {
    let mut result = Vec::new();
    let mut current = Vec::new();
    backtrack(coins, amount, 0, &mut current, &mut result);
    result
}

fn backtrack(
    coins: &[usize],
    remaining: usize,
    start: usize,
    current: &mut Vec<usize>,
    result: &mut Vec<Vec<usize>>,
) {
    if remaining == 0 {
        result.push(current.clone());
        return;
    }
    if start >= coins.len() {
        return;
    }

    // 不选当前硬币
    backtrack(coins, remaining, start + 1, current, result);

    // 选当前硬币（可重复）
    if coins[start] <= remaining {
        current.push(coins[start]);
        backtrack(coins, remaining - coins[start], start, current, result);
        current.pop();
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_min_coins_basic() {
        let coins = vec![1, 2, 5];
        assert_eq!(coin_change_min(&coins, 11), Some(3));
        assert_eq!(coin_change_min(&coins, 3), Some(2));
        assert_eq!(coin_change_min(&coins, 7), Some(2));
    }

    #[test]
    fn test_min_coins_impossible() {
        let coins = vec![2, 5];
        assert_eq!(coin_change_min(&coins, 3), None);
        assert_eq!(coin_change_min(&coins, 1), None);
    }

    #[test]
    fn test_min_coins_zero() {
        let coins = vec![1, 2, 5];
        assert_eq!(coin_change_min(&coins, 0), Some(0));
    }

    #[test]
    fn test_min_coins_with_selection() {
        let coins = vec![1, 2, 5];
        let result = coin_change_min_with_coins(&coins, 11).unwrap();
        assert_eq!(result.iter().sum::<usize>(), 11);
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_ways_basic() {
        let coins = vec![1, 2, 5];
        assert_eq!(coin_change_ways(&coins, 5), 4);
        // 1+1+1+1+1, 1+1+1+2, 1+2+2, 5
    }

    #[test]
    fn test_ways_zero() {
        let coins = vec![1, 2, 5];
        assert_eq!(coin_change_ways(&coins, 0), 1);
    }

    #[test]
    fn test_all_combinations() {
        let coins = vec![1, 2, 3];
        let combinations = coin_change_all_combinations(&coins, 4);
        assert_eq!(combinations.len(), 4);
        // [1,1,1,1], [1,1,2], [2,2], [1,3]
    }

    #[test]
    fn test_classic_example() {
        // LeetCode 322 经典示例
        let coins = vec![186, 419, 83, 408];
        assert_eq!(coin_change_min(&coins, 6249), Some(20));
    }
}
