//! 计数排序实现
//!
//! 计数排序是一种非比较排序算法，适用于整数范围已知且不大的场景。
//! 时间复杂度 O(n + k)，当 k = O(n) 时为线性时间。

use crate::{AlgorithmError, SearchResult};

/// 稳定计数排序
///
/// 对输入数组进行稳定计数排序，返回新的有序数组。
/// 假设所有元素均为 [0, max_val] 范围内的非负整数。
///
/// # 算法说明
///
/// 1. **计数阶段**: 统计每个值出现的次数
/// 2. **累加阶段**: 计算前缀和，确定每个值在输出中的最终位置
/// 3. **放置阶段**: 逆序遍历输入数组，将元素稳定地放入输出数组
///
/// # 复杂度分析
///
/// - **时间复杂度**: O(n + k)，其中 n 为数组长度，k 为 max_val
/// - **空间复杂度**: O(n + k)
/// - **稳定性**: 稳定排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::counting_sort;
///
/// let data = vec![4, 2, 2, 8, 3, 3, 1];
/// let sorted = counting_sort(&data, 8).unwrap();
/// assert_eq!(sorted, vec![1, 2, 2, 3, 3, 4, 8]);
/// ```
///
/// # 错误
///
/// 若数组中存在大于 max_val 的元素，则返回 `AlgorithmError::InvalidInput`。
pub fn counting_sort(arr: &[usize], max_val: usize) -> SearchResult<Vec<usize>> {
    if arr.is_empty() {
        return Ok(vec![]);
    }

    // 验证所有元素都在 [0, max_val] 范围内
    if let Some(&v) = arr.iter().find(|&&v| v > max_val) {
        return Err(AlgorithmError::InvalidInput(format!(
            "Element {} exceeds max_val {}",
            v, max_val
        )));
    }

    // 1. 计数
    let mut count = vec![0usize; max_val + 1];
    for &val in arr {
        count[val] += 1;
    }

    // 2. 累加: count[i] 表示 <= i 的元素个数
    for i in 1..=max_val {
        count[i] += count[i - 1];
    }

    // 3. 放置: 逆序遍历保持稳定性
    let mut output = vec![0; arr.len()];
    for &val in arr.iter().rev() {
        output[count[val] - 1] = val;
        count[val] -= 1;
    }

    Ok(output)
}

/// 计数排序（原地计数版本，非稳定）
///
/// 通过累积计数直接生成输出数组，不进行稳定性保证。
/// 适用于不需要保持相等元素原始顺序的场景。
///
/// # 示例
///
/// ```
/// use formal_algorithms::counting_sort::counting_sort_unstable;
///
/// let data = vec![4, 2, 2, 8, 3, 3, 1];
/// let sorted = counting_sort_unstable(&data, 8).unwrap();
/// assert_eq!(sorted, vec![1, 2, 2, 3, 3, 4, 8]);
/// ```
pub fn counting_sort_unstable(arr: &[usize], max_val: usize) -> SearchResult<Vec<usize>> {
    if arr.is_empty() {
        return Ok(vec![]);
    }

    if let Some(&v) = arr.iter().find(|&&v| v > max_val) {
        return Err(AlgorithmError::InvalidInput(format!(
            "Element {} exceeds max_val {}",
            v, max_val
        )));
    }

    let mut count = vec![0usize; max_val + 1];
    for &val in arr {
        count[val] += 1;
    }

    let mut output = Vec::with_capacity(arr.len());
    for (val, &cnt) in count.iter().enumerate() {
        for _ in 0..cnt {
            output.push(val);
        }
    }

    Ok(output)
}

/// 计数排序泛型版本（支持可映射为整数的键）
///
/// 通过提供键提取函数，可以对任意类型进行稳定计数排序。
///
/// # 类型参数
///
/// * `T` - 元素类型
/// * `F` - 键提取函数类型
///
/// # 示例
///
/// ```
/// use formal_algorithms::counting_sort::counting_sort_by_key;
///
/// let data = vec![(3, "c"), (1, "a"), (2, "b"), (1, "d")];
/// let sorted = counting_sort_by_key(&data, 3, |x| x.0).unwrap();
/// assert_eq!(sorted, vec![(1, "a"), (1, "d"), (2, "b"), (3, "c")]);
/// ```
pub fn counting_sort_by_key<T: Clone>(
    arr: &[T],
    max_key: usize,
    key_fn: impl Fn(&T) -> usize,
) -> SearchResult<Vec<T>> {
    if arr.is_empty() {
        return Ok(vec![]);
    }

    if let Some(v) = arr.iter().find(|v| key_fn(v) > max_key) {
        return Err(AlgorithmError::InvalidInput(format!(
            "Key {} exceeds max_key {}",
            key_fn(v),
            max_key
        )));
    }

    let mut count = vec![0usize; max_key + 1];
    for item in arr {
        count[key_fn(item)] += 1;
    }

    for i in 1..=max_key {
        count[i] += count[i - 1];
    }

    let mut output = vec![arr[0].clone(); arr.len()];
    for item in arr.iter().rev() {
        let k = key_fn(item);
        output[count[k] - 1] = item.clone();
        count[k] -= 1;
    }

    Ok(output)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty() {
        let arr: Vec<usize> = vec![];
        assert_eq!(counting_sort(&arr, 0).unwrap(), Vec::<usize>::new());
    }

    #[test]
    fn test_single_element() {
        assert_eq!(counting_sort(&[5], 10).unwrap(), vec![5]);
    }

    #[test]
    fn test_basic() {
        let arr = vec![4, 2, 2, 8, 3, 3, 1];
        assert_eq!(counting_sort(&arr, 8).unwrap(), vec![1, 2, 2, 3, 3, 4, 8]);
    }

    #[test]
    fn test_stability() {
        let arr = vec![
            (3, 0),
            (1, 1),
            (2, 2),
            (1, 3),
            (3, 4),
        ];
        let sorted = counting_sort_by_key(&arr, 3, |x| x.0).unwrap();
        // 相同键的元素应保持原始相对顺序
        assert_eq!(sorted[0].1, 1);
        assert_eq!(sorted[1].1, 3);
        assert_eq!(sorted[3].1, 0);
        assert_eq!(sorted[4].1, 4);
    }

    #[test]
    fn test_invalid_input() {
        let arr = vec![1, 2, 10];
        assert!(counting_sort(&arr, 5).is_err());
    }

    #[test]
    fn test_all_same() {
        let arr = vec![5, 5, 5, 5];
        assert_eq!(counting_sort(&arr, 5).unwrap(), vec![5, 5, 5, 5]);
    }

    #[test]
    fn test_unstable_version() {
        let arr = vec![4, 2, 2, 8, 3, 3, 1];
        assert_eq!(
            counting_sort_unstable(&arr, 8).unwrap(),
            vec![1, 2, 2, 3, 3, 4, 8]
        );
    }
}
