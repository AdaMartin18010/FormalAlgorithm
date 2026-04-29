//! LeetCode 370. 区间加法
//!
//! 对长度为 n 的初始全 0 数组进行多次区间加法更新，返回最终数组。
//!
//! 对标: LeetCode 370 / docs/13-LeetCode算法面试专题/02-算法范式专题/04-前缀和与差分.md

/// 应用所有区间更新后返回最终数组。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：`length >= 1`；`updates` 中每个元素满足 `0 <= start <= end < length`。
/// - **后置条件 (Post)**：返回应用所有更新后的数组。
///
/// # 核心思路
///
/// 差分数组惰性更新：对区间 `[l, r]` 加 `inc`：`diff[l] += inc`，`diff[r+1] -= inc`。
/// 最后对 `diff` 求前缀和还原原数组。
///
/// # 复杂度分析
///
/// - **时间复杂度**：`O(n + m)` — `m` 为更新次数。
/// - **空间复杂度**：`O(n)`
pub fn get_modified_array(length: i32, updates: Vec<Vec<i32>>) -> Vec<i32> {
    let n = length as usize;
    let mut diff = vec![0; n];

    for update in updates {
        let start = update[0] as usize;
        let end = update[1] as usize;
        let inc = update[2];
        diff[start] += inc;
        if end + 1 < n {
            diff[end + 1] -= inc;
        }
    }

    let mut result = vec![0; n];
    result[0] = diff[0];
    for i in 1..n {
        result[i] = result[i - 1] + diff[i];
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        assert_eq!(
            get_modified_array(5, vec![vec![1, 3, 2], vec![2, 4, 3], vec![0, 2, -2]]),
            vec![-2, 0, 3, 5, 3]
        );
    }

    #[test]
    fn test_no_updates() {
        assert_eq!(get_modified_array(3, vec![]), vec![0, 0, 0]);
    }

    #[test]
    fn test_single_element() {
        assert_eq!(get_modified_array(1, vec![vec![0, 0, 5]]), vec![5]);
    }

    #[test]
    fn test_full_range() {
        assert_eq!(get_modified_array(4, vec![vec![0, 3, 1]]), vec![1, 1, 1, 1]);
    }
}
