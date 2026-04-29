//! LeetCode 39. 组合总和
//!
//! 给定一个无重复元素的整数数组 candidates 和一个目标整数 target，
//! 找出 candidates 中可以使数字和为目标数 target 的所有不同组合。每个数字可以被选取无限次。
//!
//! 对标: LeetCode 39 / docs/13-LeetCode算法面试专题/02-算法范式专题/09-回溯与DFS.md

/// 返回和为 target 的所有组合，同一数字可无限选取。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`candidates` 为互不相同的正整数数组，`1 <= candidates.len() <= 30`，
///   `1 <= candidates[i] <= 200`，`1 <= target <= 500`。
/// - **后置条件 (Post)**：返回所有和等于 `target` 的组合向量，每个组合为非降序排列，结果不重复。
///
/// # 回溯不变式
///
/// - `path` 为当前已选数字列表，和为 `curr_sum`。
/// - `path` 中的数字按非降序排列（通过 `start` 参数保证）。
/// - `curr_sum <= target`。
///
/// # 剪枝条件
///
/// - 若 `curr_sum > target`，剪枝（正整数保证后续只会更大）。
/// - 若 `curr_sum == target`，记录解并返回。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(S) — S 为解空间树中所有可达状态数，最坏情况指数级。
/// - **空间复杂度**：O(target / min(candidates)) — 递归栈最深为 target 除以最小候选数。
///
/// # 证明要点
/// - 不遗漏：从 `start` 开始枚举，允许重复选取同一元素，DFS 遍历了所有非降序的多重集组合。
/// - 不重复：通过限制后续选取只能从当前索引开始，避免了 `[2,3]` 和 `[3,2]` 这样的重复排列。
/// - 剪枝安全：所有候选数为正，`curr_sum > target` 时后续不可能回到 `target`，剪枝正确。
pub fn combination_sum(mut candidates: Vec<i32>, target: i32) -> Vec<Vec<i32>> {
    candidates.sort_unstable();
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut path: Vec<i32> = Vec::new();

    fn backtrack(
        candidates: &[i32],
        target: i32,
        start: usize,
        curr_sum: i32,
        path: &mut Vec<i32>,
        result: &mut Vec<Vec<i32>>,
    ) {
        if curr_sum == target {
            result.push(path.clone());
            return;
        }
        if curr_sum > target {
            return;
        }
        for i in start..candidates.len() {
            path.push(candidates[i]);
            backtrack(candidates, target, i, curr_sum + candidates[i], path, result);
            path.pop();
        }
    }

    backtrack(&candidates, target, 0, 0, &mut path, &mut result);
    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_leetcode_example_1() {
        let result = combination_sum(vec![2, 3, 6, 7], 7);
        assert_eq!(result, vec![vec![2, 2, 3], vec![7]]);
    }

    #[test]
    fn test_leetcode_example_2() {
        let result = combination_sum(vec![2, 3, 5], 8);
        assert!(result.contains(&vec![2, 2, 2, 2]));
        assert!(result.contains(&vec![2, 3, 3]));
        assert!(result.contains(&vec![3, 5]));
        assert_eq!(result.len(), 3);
    }

    #[test]
    fn test_no_solution() {
        assert!(combination_sum(vec![2], 1).is_empty());
    }

    #[test]
    fn test_single_candidate() {
        assert_eq!(combination_sum(vec![1], 1), vec![vec![1]]);
        assert_eq!(combination_sum(vec![1], 2), vec![vec![1, 1]]);
    }
}
