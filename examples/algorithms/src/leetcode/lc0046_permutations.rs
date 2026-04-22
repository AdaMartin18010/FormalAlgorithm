//! LeetCode 46. 全排列
//!
//! 给定一个不含重复数字的数组 nums，返回其所有可能的全排列。
//!
//! 对标: LeetCode 46 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md

/// 返回数组 nums 的所有全排列。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`nums` 为互不相同的整数数组，且 `1 <= nums.len() <= 6`。
/// - **后置条件 (Post)**：返回 `nums` 的所有 `n!` 个排列，每个排列为长度为 `n` 的向量，结果不重复、不遗漏。
///
/// # 回溯不变式
///
/// 设当前路径为 `path`，已使用元素标记为 `used`。
/// - `path.len() + used.iter().filter(|&&x| x).count()` 恒等于当前递归深度已处理的步数。
/// - `path` 中元素互不相同，且均为 `nums` 中的元素。
/// - 若 `path.len() == n`，则 `path` 是 `nums` 的一个合法排列。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n × n!) — 共 n! 个排列，每个排列复制代价 O(n)。
/// - **空间复杂度**：O(n) — 递归栈深度最多为 n，加上 `path` 和 `used` 的辅助空间。
///
/// # 证明要点
///
/// - 不遗漏：每一步从所有未使用元素中选择一个加入 `path`，DFS 遍历了解空间树的全部 n! 条叶子路径。
/// - 不重复：由于 `nums` 元素互异，且每层通过 `used` 保证同一元素不会在同一排列中出现两次，生成的排列两两不同。
pub fn permute(nums: Vec<i32>) -> Vec<Vec<i32>> {
    let n = nums.len();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut path: Vec<i32> = Vec::with_capacity(n);
    let mut used = vec![false; n];

    fn backtrack(
        nums: &[i32],
        n: usize,
        path: &mut Vec<i32>,
        used: &mut [bool],
        result: &mut Vec<Vec<i32>>,
    ) {
        if path.len() == n {
            result.push(path.clone());
            return;
        }
        for i in 0..n {
            if used[i] {
                continue;
            }
            used[i] = true;
            path.push(nums[i]);
            backtrack(nums, n, path, used, result);
            path.pop();
            used[i] = false;
        }
    }

    backtrack(&nums, n, &mut path, &mut used, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let nums = vec![1, 2, 3];
        let result = permute(nums);
        assert_eq!(result.len(), 6);
        assert!(result.contains(&vec![1, 2, 3]));
        assert!(result.contains(&vec![1, 3, 2]));
        assert!(result.contains(&vec![2, 1, 3]));
        assert!(result.contains(&vec![2, 3, 1]));
        assert!(result.contains(&vec![3, 1, 2]));
        assert!(result.contains(&vec![3, 2, 1]));
    }

    #[test]
    fn test_leetcode_example_2() {
        let nums = vec![0, 1];
        assert_eq!(permute(nums), vec![vec![0, 1], vec![1, 0]]);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(permute(vec![1]), vec![vec![1]]);
    }

    #[test]
    fn test_four_elements() {
        assert_eq!(permute(vec![1, 2, 3, 4]).len(), 24);
    }
}
