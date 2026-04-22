//! LeetCode 470. 用 Rand7() 实现 Rand10()
//!
//! 已有方法 `rand7()` 可生成 1 到 7 范围内的均匀随机整数，试利用此方法
//! 生成 1 到 10 范围内的均匀随机整数。
//!
//! # 核心思路
//!
//! **拒绝采样（Rejection Sampling）**：
//! 1. 调用两次 `rand7()`，构造一个均匀分布的整数 `num ∈ [0, 48]`：
//!    `num = (rand7() - 1) * 7 + (rand7() - 1)`。
//! 2. 若 `num < 40`，则 `num % 10 + 1` 即为 `rand10()` 的结果。
//! 3. 若 `num >= 40`，拒绝本次采样，重新生成。
//!
//! # 正确性说明
//!
//! - `[0, 48]` 共 49 个整数，每个出现的概率均为 `1/49`。
//! - 取 `[0, 39]` 共 40 个整数，每个出现的条件概率为 `1/40`。
//! - `num % 10` 将 `[0, 39]` 均分为 10 组，每组 4 个，故结果为 `[0, 9]` 均匀分布。
//! - 加 1 后得到 `[1, 10]` 均匀分布。
//!
//! # 复杂度分析
//!
//! - **期望时间复杂度**：O(1)。每次循环接受概率为 `40/49`，期望循环次数为 `49/40 ≈ 1.225`。
//! - **空间复杂度**：O(1)。

use rand::Rng;

/// 生成 1 到 7 的均匀随机整数（题目给定）。
fn rand7() -> i32 {
    rand::thread_rng().gen_range(1..=7)
}

/// 利用 `rand7()` 生成 1 到 10 的均匀随机整数。
pub fn rand10() -> i32 {
    loop {
        let a = rand7() - 1; // 0..6
        let b = rand7() - 1; // 0..6
        let num = a * 7 + b; // 0..48，均匀分布
        if num < 40 {
            return num % 10 + 1; // 1..10，均匀分布
        }
        // num ∈ [40, 48] 时拒绝，重新采样
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_rand10_range() {
        for _ in 0..1000 {
            let v = rand10();
            assert!(v >= 1 && v <= 10, "rand10() = {} out of range", v);
        }
    }

    #[test]
    fn test_rand10_uniformity_approximate() {
        let mut count = [0usize; 11];
        const N: usize = 10_000;
        for _ in 0..N {
            let v = rand10() as usize;
            count[v] += 1;
        }
        // 粗略均匀性检查：每个数字出现次数应在期望值的 ±20% 内
        let expected = N / 10;
        let low = expected * 8 / 10;
        let high = expected * 12 / 10;
        for v in 1..=10 {
            assert!(
                count[v] >= low && count[v] <= high,
                "value {} count {} out of range [{}, {}]",
                v,
                count[v],
                low,
                high
            );
        }
    }
}
