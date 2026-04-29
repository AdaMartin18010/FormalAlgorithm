//! LeetCode 312. 戳气球 / Burst Balloons
//!
//! 有 n 个气球，编号为 0 到 n-1，每个气球上都标有一个数字，这些数字存在数组 nums 中。
//!
//! 现在要求你戳破所有的气球。戳破第 i 个气球，你可以获得 nums[left] * nums[i] * nums[right] 个硬币。
//! 这里的 left 和 right 表示和 i 相邻的两个气球的序号。注意当你戳破了气球 i 后，
//! 气球 left 和气球 right 就变成了相邻的气球。
//!
//! 求所能获得硬币的最大数量。
//!
//! 题目链接: <https://leetcode.com/problems/burst-balloons/>
//! 难度: Hard
//!
//! 对标: docs/13-LeetCode算法面试专题/02-算法范式专题/08-动态规划.md §3.6
//!
//! ## 形式化规约
//!
//! - **输入**: 数组 $nums[0..n-1]$，$nums[i] > 0$
//! - **输出**: $\max_{\text{戳破顺序}} \sum \text{coins}(i, \text{left}, \text{right})$
//! - **前置条件**: $1 \leq n \leq 300$，$0 \leq nums[i] \leq 100$
//! - **后置条件**: 返回最大可获得硬币数
//!
//! ## 技巧：逆向思考（加气球而非戳气球）
//!
//! 正向戳气球会导致相邻关系动态变化，难以设计状态。
//! **逆向思考**：假设所有气球已戳破，现在逐个"添加"气球回来。
//! 最后添加的气球 $k$ 将区间 $[i,j]$ 分为 $[i,k]$ 和 $[k,j]$，
//! 获得硬币 $val[i] \times val[k] \times val[j]$。
//!
//! ## 状态定义
//!
//! 在数组两端添加虚拟气球 $val[0] = val[n+1] = 1$。
//! $dp[i][j]$ = 开区间 $(i, j)$ 内所有气球都戳破（或说都添加回来）能获得的最大硬币数。
//!
//! ## 状态转移方程
//!
//! $$ dp[i][j] = \max_{i < k < j} \{ dp[i][k] + dp[k][j] + val[i] \cdot val[k] \cdot val[j] \} $$
//!
//! ## 最优子结构引理
//!
//! **引理**: 设 $k$ 为开区间 $(i,j)$ 内最后一个被戳破（或第一个被添加）的气球，则
//! $$ OPT(i,j) = OPT(i,k) + OPT(k,j) + val[i] \cdot val[k] \cdot val[j] $$
//!
//! **证明**: 当 $k$ 是 $(i,j)$ 内最后一个被戳破的气球时，此时 $i$ 和 $j$ 必然相邻于 $k$ 两侧
//!（因为 $(i,k)$ 和 $(k,j)$ 内的气球都已被戳破）。因此戳破 $k$ 获得的硬币恰好为
//! $val[i] \cdot val[k] \cdot val[j]$。而 $(i,k)$ 和 $(k,j)$ 的戳破顺序相互独立，
//! 各自必为最优解，否则替换为更优子解可提升整体解。$\square$

/// 计算戳破所有气球能获得的最大硬币数。
///
/// # 参数
///
/// * `nums` - 气球上的数字数组
///
/// # 返回值
///
/// 最大可获得硬币数。
///
/// # 复杂度分析
///
/// | 指标 | 值 | 说明 |
/// |------|-----|------|
/// | 时间复杂度 | $O(n^3)$ | 区间长度 × 区间起点 × 分割点 |
/// | 空间复杂度 | $O(n^2)$ | 二维 DP 表 |
///
/// # 正确性证明
///
/// **定理**: 算法返回最大硬币数。
///
/// **证明** (区间长度归纳法):
///
/// 对区间长度 $len = j - i$ 进行归纳。
///
/// - **基例**: $len = 1$（即 $j = i + 1$），开区间 $(i,j)$ 内无气球，$dp[i][j] = 0$，正确。
/// - **归纳假设**: 假设对所有长度 $< len$ 的区间，$dp[i][j]$ 已正确计算。
/// - **归纳步骤**: 对长度 $len$ 的区间 $(i,j)$，枚举最后一个被戳破的气球 $k \in (i,j)$：
///   由归纳假设，$dp[i][k]$ 和 $dp[k][j]$ 分别为两个子区间的最优解。
///   由引理，以 $k$ 为最后戳破点的最优值为 $dp[i][k] + dp[k][j] + val[i] \cdot val[k] \cdot val[j]$。
///   对所有 $k$ 取最大值即得 $dp[i][j] = OPT(i,j)$。$\square$
pub fn max_coins(nums: Vec<i32>) -> i32 {
    let n = nums.len();
    // 扩展数组，两端添加虚拟气球 1
    let mut val = vec![1; n + 2];
    for i in 0..n {
        val[i + 1] = nums[i];
    }

    // dp[i][j] = 开区间 (i, j) 能获得的最大硬币
    let mut dp = vec![vec![0; n + 2]; n + 2];

    // 按区间长度从小到大填表
    for len in 2..=n + 1 {
        for i in 0..=n + 1 - len {
            let j = i + len;
            for k in i + 1..j {
                dp[i][j] = dp[i][j].max(dp[i][k] + dp[k][j] + val[i] * val[k] * val[j]);
            }
        }
    }

    dp[0][n + 1]
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(max_coins(vec![3, 1, 5, 8]), 167);
        // Explanation: nums = [3,1,5,8] --> [3,5,8] --> [3,8] --> [8] --> []
        // coins = 3*1*5 + 3*5*8 + 1*3*8 + 1*8*1 = 15 + 120 + 24 + 8 = 167
    }

    #[test]
    fn test_example_2() {
        assert_eq!(max_coins(vec![1, 5]), 10); // 1*1*5 + 1*5*1 = 5 + 5 = 10
    }

    #[test]
    fn test_single() {
        assert_eq!(max_coins(vec![5]), 5); // 1*5*1 = 5
    }

    #[test]
    fn test_two() {
        assert_eq!(max_coins(vec![3, 1]), 6); // 1*3*1 + 1*1*1 = 3 + 1 = 4... wait
        // Actually: [3,1] -> [1] (3*1*1=3) -> [] (1*1*1=1), total=4
        // Or: [3,1] -> [3] (1*1*3=3) -> [] (1*3*1=3), total=6
        // Optimal is to burst 1 first: 1*3*1 + 1*1*1 = 4... no wait
        // Let's trace: burst 1 first: coins = 3*1*1 = 3, then burst 3: 1*3*1 = 3, total = 6
        assert_eq!(max_coins(vec![3, 1]), 6);
    }

    #[test]
    fn test_all_ones() {
        assert_eq!(max_coins(vec![1, 1, 1, 1]), 4); // Any order gives 1+1+1+1=4
    }

    #[test]
    fn test_zeros() {
        assert_eq!(max_coins(vec![0, 0]), 0);
    }
}
