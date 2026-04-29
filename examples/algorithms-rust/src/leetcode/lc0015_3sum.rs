//! LeetCode 15. 三数之和
//!
//! 给你一个整数数组 nums，判断是否存在三元组 [nums[i], nums[j], nums[k]]
//! 满足 i != j, i != k, j != k，且 nums[i] + nums[j] + nums[k] == 0。
//! 返回所有和为 0 且不重复的三元组。
//!
//! 对标: LeetCode 15 / docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md

/// 找出数组中所有和为 0 的不重复三元组。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为整数数组，长度 ∈ [0, 5000]，元素值 ∈ [-10^5, 10^5]。
/// - **后置条件 (Post)**：返回所有满足 i < j < k 且 nums[i] + nums[j] + nums[k] == 0 的三元组列表。
///   结果中不包含重复的三元组，每个三元组内部按非降序排列。
///
/// # 核心思路
///
/// 排序 + 对撞指针：
/// 1. 将数组排序，得到非降序序列。
/// 2. 固定第一个元素 nums[i]，问题转化为在 i 右侧寻找两数之和为 -nums[i]。
/// 3. 使用对撞指针 l, r 在 [i+1, n-1] 范围内搜索。
/// 4. 通过排序后的去重策略保证结果唯一性。
///
/// # 循环不变式（对撞指针阶段）
///
/// 设固定 i，左指针 l = i+1，右指针 r = n-1。
/// 不变式：所有满足 j < l 或 k > r 的配对 (j,k) 均已被考察或不可能构成解。
///
/// **维护**：
/// - 初始 l = i+1, r = n-1，显然成立。
/// - 计算 s = nums[i] + nums[l] + nums[r]：
///   * s == 0：记录解，并收缩 l,r 以跳过重复值。
///   * s < 0：nums[l] 太小，需要更大的左端点，l += 1。
///   * s > 0：nums[r] 太大，需要更小的右端点，r -= 1。
/// - 每次移动都排除了当前 l 或 r 不可能再参与构成解的情况。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n^2) — 外层固定 i 为 O(n)，内层对撞指针为 O(n)。
/// - **空间复杂度**：O(1) — 不计输出空间，仅使用常数个指针和变量。
///   排序需要 O(log n) 栈空间（TimSort 等原地排序）。
///
/// # 证明要点
///
/// - 不遗漏解的证明见 `docs/13-LeetCode算法面试专题/02-算法范式专题/02-双指针.md`
/// - 核心：排序后，对固定的 i，所有可能的两数之和解必在 [i+1, n-1] 内，
///   且对撞指针的移动策略保证每个配对至多被跳过一次。
pub fn three_sum(mut nums: Vec<i32>) -> Vec<Vec<i32>> {
    nums.sort_unstable();
    let n = nums.len();
    let mut result: Vec<Vec<i32>> = Vec::new();

    for i in 0..n.saturating_sub(2) {
        // 去重：跳过相同的 nums[i]
        if i > 0 && nums[i] == nums[i - 1] {
            continue;
        }

        // 剪枝：若最小三数之和 > 0，后续不可能有解
        if nums[i] + nums[i + 1] + nums[i + 2] > 0 {
            break;
        }
        // 剪枝：若当前 nums[i] 与最大两数之和 < 0，当前 i 无解
        if nums[i] + nums[n - 2] + nums[n - 1] < 0 {
            continue;
        }

        let _target = -nums[i];
        let mut left = i + 1;
        let mut right = n - 1;

        while left < right {
            let total = nums[i] + nums[left] + nums[right];
            if total == 0 {
                result.push(vec![nums[i], nums[left], nums[right]]);
                // 跳过重复值
                while left < right && nums[left] == nums[left + 1] {
                    left += 1;
                }
                while left < right && nums[right] == nums[right - 1] {
                    right -= 1;
                }
                left += 1;
                right -= 1;
            } else if total < 0 {
                left += 1;
            } else {
                right -= 1;
            }
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        let result = three_sum(vec![-1, 0, 1, 2, -1, -4]);
        assert_eq!(result, vec![vec![-1, -1, 2], vec![-1, 0, 1]]);
    }

    #[test]
    fn test_example_2() {
        let result = three_sum(vec![0, 1, 1]);
        assert!(result.is_empty());
    }

    #[test]
    fn test_example_3() {
        let result = three_sum(vec![0, 0, 0]);
        assert_eq!(result, vec![vec![0, 0, 0]]);
    }

    #[test]
    fn test_empty() {
        assert!(three_sum(vec![]).is_empty());
    }

    #[test]
    fn test_less_than_three() {
        assert!(three_sum(vec![1, 2]).is_empty());
    }

    #[test]
    fn test_all_positive() {
        assert!(three_sum(vec![1, 2, 3]).is_empty());
    }

    #[test]
    fn test_all_negative() {
        assert!(three_sum(vec![-3, -2, -1]).is_empty());
    }

    #[test]
    fn test_many_duplicates() {
        let result = three_sum(vec![0, 0, 0, 0, 0]);
        assert_eq!(result, vec![vec![0, 0, 0]]);
    }
}
