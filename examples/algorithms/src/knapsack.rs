//! 0/1 背包问题实现
//!
//! 0/1 背包问题是动态规划中最经典的模型之一：
//! 给定 n 个物品，每个物品有重量 weight[i] 和价值 value[i]，
//! 在总重量不超过容量 W 的前提下，选择物品使总价值最大。
//!
//! 对标: CLRS 4th Ed. Ch 14.1（Rod Cutting 后自然延伸的经典 DP 例题）；
//! MIT 6.006 Dynamic Programming 模块；Stanford CS161 核心教学内容。
//!
//! ## 动态规划状态转移
//!
//! `dp[i][w]` = 考虑前 i 个物品、容量为 w 时的最大价值
//!
//! 状态转移：
//! - 不选第 i 个物品：`dp[i][w] = dp[i-1][w]`
//! - 选第 i 个物品：`dp[i][w] = dp[i-1][w-weight[i]] + value[i]`（若 w ≥ weight[i]）
//!
//! `dp[i][w] = max(dp[i-1][w], dp[i-1][w-weight[i]] + value[i])`
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：O(n × W)
//! - **空间复杂度**：
//!   - 基础版本：O(n × W)
//!   - 空间优化版本：O(W)
//!
//! ## 变体问题
//!
//! - **完全背包**：每种物品无限件（unbounded knapsack）
//! - **多重背包**：每种物品有限件（bounded knapsack）
//! - **分数背包**：可拆分物品，贪心即可（O(n log n)）

/// 0/1 背包问题：返回最大价值
///
/// # 参数
///
/// * `weights` - 每个物品的重量
/// * `values` - 每个物品的价值
/// * `capacity` - 背包容量
///
/// # 返回值
///
/// 最大总价值
///
/// # 示例
///
/// ```
/// use formal_algorithms::knapsack::knapsack_01;
///
/// let weights = vec![2, 3, 4, 5];
/// let values = vec![3, 4, 5, 6];
/// let capacity = 5;
///
/// assert_eq!(knapsack_01(&weights, &values, capacity), 7); // 选物品1(重2价3) + 物品2(重3价4)
/// ```
pub fn knapsack_01(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    if n == 0 || capacity == 0 {
        return 0;
    }

    // dp[w] = 容量为 w 时的最大价值
    let mut dp = vec![0; capacity + 1];

    for i in 0..n {
        // 倒序遍历容量，避免重复选择
        for w in (weights[i]..=capacity).rev() {
            dp[w] = dp[w].max(dp[w - weights[i]] + values[i]);
        }
    }

    dp[capacity]
}

/// 0/1 背包问题：返回最大价值及选择的物品索引
///
/// # 返回值
///
/// `(max_value, selected_indices)`
///
/// # 示例
///
/// ```
/// use formal_algorithms::knapsack::knapsack_01_with_selection;
///
/// let weights = vec![2, 3, 4, 5];
/// let values = vec![3, 4, 5, 6];
/// let capacity = 5;
///
/// let (max_value, selected) = knapsack_01_with_selection(&weights, &values, capacity);
/// assert_eq!(max_value, 7);
/// assert_eq!(selected, vec![0, 1]); // 选择第0个和第1个物品
/// ```
pub fn knapsack_01_with_selection(
    weights: &[usize],
    values: &[usize],
    capacity: usize,
) -> (usize, Vec<usize>) {
    let n = weights.len();
    if n == 0 || capacity == 0 {
        return (0, vec![]);
    }

    let mut dp = vec![vec![0; capacity + 1]; n + 1];

    for i in 1..=n {
        for w in 0..=capacity {
            dp[i][w] = dp[i - 1][w];
            if w >= weights[i - 1] {
                dp[i][w] = dp[i][w].max(dp[i - 1][w - weights[i - 1]] + values[i - 1]);
            }
        }
    }

    // 回溯找出选择的物品
    let mut selected = Vec::new();
    let mut w = capacity;
    for i in (1..=n).rev() {
        if dp[i][w] != dp[i - 1][w] {
            selected.push(i - 1);
            w -= weights[i - 1];
        }
    }
    selected.reverse();

    (dp[n][capacity], selected)
}

/// 完全背包问题：每种物品无限件
///
/// 状态转移：正序遍历容量（允许重复选择）
///
/// # 示例
///
/// ```
/// use formal_algorithms::knapsack::unbounded_knapsack;
///
/// let weights = vec![1, 3, 4];
/// let values = vec![15, 20, 30];
/// let capacity = 4;
///
/// // 选4个重量1的物品：4×15 = 60，优于其他组合
/// assert_eq!(unbounded_knapsack(&weights, &values, capacity), 60);
/// ```
pub fn unbounded_knapsack(weights: &[usize], values: &[usize], capacity: usize) -> usize {
    let n = weights.len();
    if n == 0 || capacity == 0 {
        return 0;
    }

    let mut dp = vec![0; capacity + 1];

    for i in 0..n {
        for w in weights[i]..=capacity {
            dp[w] = dp[w].max(dp[w - weights[i]] + values[i]);
        }
    }

    dp[capacity]
}

/// 分数背包问题：物品可拆分，贪心求解
///
/// 按单位重量价值从高到低排序，依次选取直到背包装满。
///
/// # 返回值
///
/// 最大总价值（f64，允许分数）
///
/// # 示例
///
/// ```
/// use formal_algorithms::knapsack::fractional_knapsack;
///
/// let weights = vec![10, 20, 30];
/// let values = vec![60, 100, 120];
/// let capacity = 50;
///
/// // 单位价值：6, 5, 4。先取10+20=30，再取20/30的第三个物品
/// // 总价值 = 60 + 100 + 120×(20/30) = 240
/// assert_eq!(fractional_knapsack(&weights, &values, capacity), 240.0);
/// ```
pub fn fractional_knapsack(weights: &[usize], values: &[usize], capacity: usize) -> f64 {
    let n = weights.len();
    if n == 0 || capacity == 0 {
        return 0.0;
    }

    let mut items: Vec<(usize, usize, f64)> = weights
        .iter()
        .zip(values.iter())
        .map(|(&w, &v)| (w, v, v as f64 / w as f64))
        .collect();

    // 按单位价值降序排列
    items.sort_by(|a, b| b.2.partial_cmp(&a.2).unwrap());

    let mut total_value = 0.0;
    let mut remaining = capacity;

    for (w, v, ratio) in items {
        if remaining == 0 {
            break;
        }
        if w <= remaining {
            total_value += v as f64;
            remaining -= w;
        } else {
            total_value += remaining as f64 * ratio;
            remaining = 0;
        }
    }

    total_value
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_knapsack_01_basic() {
        let weights = vec![2, 3, 4, 5];
        let values = vec![3, 4, 5, 6];
        assert_eq!(knapsack_01(&weights, &values, 5), 7);
    }

    #[test]
    fn test_knapsack_01_empty() {
        assert_eq!(knapsack_01(&[], &[], 10), 0);
    }

    #[test]
    fn test_knapsack_01_zero_capacity() {
        let weights = vec![1, 2, 3];
        let values = vec![10, 20, 30];
        assert_eq!(knapsack_01(&weights, &values, 0), 0);
    }

    #[test]
    fn test_knapsack_01_large() {
        let weights = vec![1, 2, 3, 8, 7, 4];
        let values = vec![20, 5, 10, 40, 15, 25];
        assert_eq!(knapsack_01(&weights, &values, 10), 60); // 1+2+3+4=10, value=20+5+10+25=60
    }

    #[test]
    fn test_knapsack_with_selection() {
        let weights = vec![2, 3, 4, 5];
        let values = vec![3, 4, 5, 6];
        let (max_value, selected) = knapsack_01_with_selection(&weights, &values, 5);
        assert_eq!(max_value, 7);
        assert_eq!(selected, vec![0, 1]);
    }

    #[test]
    fn test_unbounded_knapsack() {
        let weights = vec![1, 3, 4];
        let values = vec![15, 20, 30];
        assert_eq!(unbounded_knapsack(&weights, &values, 4), 60);
    }

    #[test]
    fn test_fractional_knapsack() {
        let weights = vec![10, 20, 30];
        let values = vec![60, 100, 120];
        assert_eq!(fractional_knapsack(&weights, &values, 50), 240.0);
    }

    #[test]
    fn test_knapsack_with_selection_multiple() {
        let weights = vec![1, 2, 3, 8, 7, 4];
        let values = vec![20, 5, 10, 40, 15, 25];
        let (max_value, selected) = knapsack_01_with_selection(&weights, &values, 10);
        assert_eq!(max_value, 60);
        // 验证选中物品的重量不超过容量，且价值之和等于最优值
        let total_weight: usize = selected.iter().map(|&i| weights[i]).sum();
        let total_value: usize = selected.iter().map(|&i| values[i]).sum();
        assert!(total_weight <= 10);
        assert_eq!(total_value, 60);
    }
}
