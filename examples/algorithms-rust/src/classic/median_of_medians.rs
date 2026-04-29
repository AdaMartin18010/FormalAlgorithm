//! Median of Medians 算法实现
//!
//! Median of Medians（中位数的中位数）是一种确定性选择算法，
//! 用于在 worst-case O(n) 时间内找出无序数组中的第 k 小元素。
//!
//! 对标: CLRS 4th Ed. Section 9.3（Selection in Worst-case Linear Time）；
//! MIT 6.046J / Stanford CS161 高级算法课程核心内容。
//!
//! ## 核心思想
//!
//! 快速选择 (QuickSelect) 的期望时间是 O(n)，但最坏情况是 O(n²)。
//! Median of Medians 通过**精心选择的 pivot**，保证每次递归至少淘汰 30% 的元素，
//! 从而将最坏情况控制在 O(n)。
//!
//! ## 算法步骤
//!
//! 1. 将数组分为若干组，每组 5 个元素
//! 2. 找出每组的中位数
//! 3. 递归找出这些中位数的中位数作为 pivot
//! 4. 用 pivot 划分数组
//! 5. 根据 k 与 pivot 位置的关系，递归处理左半或右半
//!
//! ## 为什么每组 5 个？
//!
//! 每组大小为 5 是使得递归方程 $T(n) \leq T(n/5) + T(7n/10) + O(n)$ 能收敛到 O(n) 的最小奇数。
//!
//! - 中位数的中位数保证至少 $3n/10 - 6$ 个元素小于等于 pivot
//! - 同理，至少 $3n/10 - 6$ 个元素大于等于 pivot
//! - 因此每次递归最多处理 $7n/10 + 6$ 个元素
//!
//! ## 复杂度分析
//!
//! - **时间复杂度**：O(n) —— 最坏情况保证
//! - **空间复杂度**：O(log n) —— 递归栈深度
//! - **常数因子**：较大，实际中 QuickSelect + 随机 pivot 通常更快
//!
//! ## 实际应用
//!
//! - 理论保证 worst-case 的选择场景
//! - 作为其他算法的子程序（如 weighted median）
//! - 教学用途：展示如何通过递归分析设计 worst-case 高效算法

/// Median of Medians 选择算法
///
/// 返回数组中第 k 小（0-based）的元素。
/// 即：若数组排序后，返回索引为 k 的元素。
///
/// # 参数
///
/// * `arr` - 输入数组（会被重新排列）
/// * `k` - 目标排名（0-based，0 = 最小，arr.len()-1 = 最大）
///
/// # 返回值
///
/// 第 k 小元素的引用
///
/// #  Panic
///
/// 若 k >= arr.len()，则 panic。
///
/// # 示例
///
/// ```
/// use formal_algorithms::median_of_medians::select;
///
/// let mut arr = vec![12, 3, 5, 7, 4, 19, 26];
/// let median = select(&mut arr, 3); // 第4小（中位数）
/// assert_eq!(*median, 7);
/// ```
///
/// # 复杂度
///
/// - 时间：O(n) 最坏情况
/// - 空间：O(log n) 递归栈
pub fn select<T: Ord>(arr: &mut [T], k: usize) -> &T {
    assert!(!arr.is_empty(), "select on empty array");
    assert!(k < arr.len(), "k out of bounds");

    let n = arr.len();
    if n <= 5 {
        arr.sort();
        return &arr[k];
    }

    // Step 1: 分为每组5个，找出每组中位数
    let num_groups = (n + 4) / 5;
    let mut medians: Vec<usize> = Vec::with_capacity(num_groups);

    for g in 0..num_groups {
        let start = g * 5;
        let end = ((g + 1) * 5).min(n);
        let group = &mut arr[start..end];
        group.sort();
        let median_idx = start + group.len() / 2;
        medians.push(median_idx);
    }

    // Step 2: 递归找出中位数的中位数
    let median_of_medians_idx = if medians.len() == 1 {
        medians[0]
    } else {
        let mid = medians.len() / 2;
        let pivot_idx = select_by_indices(arr, &medians, mid);
        pivot_idx
    };

    // Step 3: 将 pivot 放到数组末尾（ Lomuto 分区方案）
    let last = n - 1;
    arr.swap(median_of_medians_idx, last);

    // Step 4: 分区
    let pivot_pos = partition(arr, last);

    // Step 5: 递归
    match pivot_pos.cmp(&k) {
        std::cmp::Ordering::Equal => &arr[pivot_pos],
        std::cmp::Ordering::Greater => select(&mut arr[..pivot_pos], k),
        std::cmp::Ordering::Less => select(&mut arr[pivot_pos + 1..], k - pivot_pos - 1),
    }
}

/// 辅助函数：在数组中根据索引列表选择第 k 小元素，返回该元素在数组中的位置
fn select_by_indices<T: Ord>(arr: &mut [T], indices: &[usize], k: usize) -> usize {
    let n = indices.len();
    if n <= 5 {
        let mut sorted = indices.to_vec();
        sorted.sort_by_key(|&i| &arr[i]);
        sorted[k]
    } else {
        let num_groups = (n + 4) / 5;
        let mut medians = Vec::with_capacity(num_groups);

        for g in 0..num_groups {
            let start = g * 5;
            let end = ((g + 1) * 5).min(n);
            let mut group: Vec<usize> = indices[start..end].to_vec();
            group.sort_by_key(|&i| &arr[i]);
            medians.push(group[group.len() / 2]);
        }

        let mom_idx = if medians.len() == 1 {
            medians[0]
        } else {
            let mid = medians.len() / 2;
            select_by_indices(arr, &medians, mid)
        };

        // 分区
        let last_idx = n - 1;
        let last_val_idx = indices[last_idx];
        arr.swap(mom_idx, last_val_idx);

        let mut store_idx = 0;
        for i in 0..last_idx {
            if arr[indices[i]] < arr[last_val_idx] {
                arr.swap(indices[store_idx], indices[i]);
                store_idx += 1;
            }
        }
        arr.swap(indices[store_idx], last_val_idx);

        let pivot_pos = store_idx;
        match pivot_pos.cmp(&k) {
            std::cmp::Ordering::Equal => indices[pivot_pos],
            std::cmp::Ordering::Greater => {
                let left: Vec<usize> = indices[..pivot_pos].to_vec();
                select_by_indices(arr, &left, k)
            }
            std::cmp::Ordering::Less => {
                let right: Vec<usize> = indices[pivot_pos + 1..].to_vec();
                select_by_indices(arr, &right, k - pivot_pos - 1)
            }
        }
    }
}

/// Lomuto 分区方案
///
/// 假设 pivot 已在数组末尾（索引 last）。
/// 返回 pivot 的最终位置。
fn partition<T: Ord>(arr: &mut [T], last: usize) -> usize {
    let mut i = 0;
    for j in 0..last {
        if arr[j] <= arr[last] {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, last);
    i
}

/// 快速查找数组中位数（Median of Medians 实现）
///
/// 对于偶数长度数组，返回下中位数（第 n/2 - 1 小元素，0-based）。
///
/// # 示例
///
/// ```
/// use formal_algorithms::median_of_medians::median;
///
/// let mut arr = vec![12, 3, 5, 7, 4, 19, 26];
/// assert_eq!(*median(&mut arr), 7);
///
/// let mut arr2 = vec![1, 2, 3, 4];
/// assert_eq!(*median(&mut arr2), 2); // 下中位数
/// ```
pub fn median<T: Ord>(arr: &mut [T]) -> &T {
    let n = arr.len();
    assert!(!arr.is_empty(), "median on empty array");
    select(arr, (n - 1) / 2)
}

/// 快速查找数组中的任意百分位数
///
/// # 参数
///
/// * `percentile` — 0.0 到 1.0 之间的值，0.0 = 最小值，1.0 = 最大值
///
/// # 示例
///
/// ```
/// use formal_algorithms::median_of_medians::percentile;
///
/// let mut arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
/// assert_eq!(*percentile(&mut arr, 0.0), 1);  // 最小值
/// assert_eq!(*percentile(&mut arr, 0.5), 5);  // 下中位数
/// assert_eq!(*percentile(&mut arr, 1.0), 10); // 最大值
/// ```
pub fn percentile<T: Ord>(arr: &mut [T], percentile: f64) -> &T {
    assert!(!arr.is_empty());
    assert!((0.0..=1.0).contains(&percentile));
    let k = ((arr.len() - 1) as f64 * percentile).floor() as usize;
    let k = k.min(arr.len() - 1);
    select(arr, k)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_select_basic() {
        let mut arr = vec![12, 3, 5, 7, 4, 19, 26];
        assert_eq!(*select(&mut arr, 0), 3);  // 最小
        assert_eq!(*select(&mut arr, 3), 7);  // 中位数
        assert_eq!(*select(&mut arr, 6), 26); // 最大
    }

    #[test]
    fn test_select_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        for i in 0..5 {
            assert_eq!(*select(&mut arr, i), i + 1);
        }
    }

    #[test]
    fn test_select_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        for i in 0..5 {
            assert_eq!(*select(&mut arr, i), i + 1);
        }
    }

    #[test]
    fn test_select_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        assert_eq!(*select(&mut arr, 0), 1);
        assert_eq!(*select(&mut arr, 4), 4);
        assert_eq!(*select(&mut arr, 8), 9);
    }

    #[test]
    fn test_median() {
        let mut arr = vec![12, 3, 5, 7, 4, 19, 26];
        assert_eq!(*median(&mut arr), 7);

        let mut arr2 = vec![1, 2, 3, 4];
        assert_eq!(*median(&mut arr2), 2);
    }

    #[test]
    fn test_large_random() {
        let mut arr: Vec<i32> = (0..1000).map(|i| (i * 7919) % 10000).collect();
        let mut sorted = arr.clone();
        sorted.sort();
        for k in [0, 1, 100, 500, 999] {
            let result = *select(&mut arr, k);
            assert_eq!(result, sorted[k], "mismatch at k={}", k);
        }
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        assert_eq!(*select(&mut arr, 0), 42);
        assert_eq!(*median(&mut arr), 42);
    }

    #[test]
    fn test_percentile() {
        let mut arr = vec![1, 2, 3, 4, 5, 6, 7, 8, 9, 10];
        assert_eq!(*percentile(&mut arr, 0.0), 1);
        assert_eq!(*percentile(&mut arr, 0.5), 5);
        assert_eq!(*percentile(&mut arr, 1.0), 10);
    }
}
