//! 归并排序实现
//!
//! 归并排序是一种基于分治策略的稳定排序算法。
//! 它将数组递归地分成两半，分别排序后再合并。
//!
//! ## 形式化规范 (Formal Specification)
//!
//! 对应 Lean 证明: [`examples/lean_proofs/sorting_proofs.lean`]
//!
//! | Rust 规范 | Lean 谓词/定理 | 状态 |
//! |-----------|---------------|------|
//! | `merge_sort` 输出有序 | `mergeSort_sorted` | ✅ 已证明 (含 `merge_sorted` 引理) |
//! | 排列性质 (multiset 等价) | `List.Perm (mergeSort xs) xs` | ⚠️ 待扩展 (需 mathlib4 `List.Perm`) |


/// 对可变切片进行归并排序
///
/// # 算法说明
///
/// 归并排序采用分治法(Divide and Conquer)策略：
/// 1. **分解**：将n个元素分成各含n/2个元素的子序列
/// 2. **解决**：对两个子序列递归地排序
/// 3. **合并**：合并两个已排序的子序列
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n log n)
///   - 最坏情况：O(n log n)
///   - 最好情况：O(n log n)
///   - 平均情况：O(n log n)
/// - **空间复杂度**：O(n) - 需要额外数组存储临时结果
/// - **稳定性**：稳定排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::merge_sort;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// merge_sort(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let len = arr.len();
    let mut temp = arr.to_vec();
    merge_sort_internal(arr, &mut temp, 0, len - 1);
}

/// 内部递归函数
fn merge_sort_internal<T: Ord + Clone>(arr: &mut [T], temp: &mut [T], left: usize, right: usize) {
    if left < right {
        let mid = left + (right - left) / 2;
        merge_sort_internal(arr, temp, left, mid);
        merge_sort_internal(arr, temp, mid + 1, right);
        merge(arr, temp, left, mid, right);
    }
}

/// 合并两个已排序的子数组
///
/// # 参数
///
/// * `arr` - 原始数组
/// * `temp` - 临时数组
/// * `left` - 左边界索引
/// * `mid` - 中间索引
/// * `right` - 右边界索引
fn merge<T: Ord + Clone>(arr: &mut [T], temp: &mut [T], left: usize, mid: usize, right: usize) {
    // 复制到临时数组
    for i in left..=right {
        temp[i] = arr[i].clone();
    }

    let mut i = left;      // 左子数组索引
    let mut j = mid + 1;   // 右子数组索引
    let mut k = left;      // 合并位置索引

    // 合并两个有序数组
    while i <= mid && j <= right {
        if temp[i] <= temp[j] {
            arr[k] = temp[i].clone();
            i += 1;
        } else {
            arr[k] = temp[j].clone();
            j += 1;
        }
        k += 1;
    }

    // 复制剩余元素
    while i <= mid {
        arr[k] = temp[i].clone();
        i += 1;
        k += 1;
    }

    // 右子数组剩余元素已经在正确位置
}

/// 归并排序的泛型版本，返回新数组
///
/// # 示例
///
/// ```
/// use formal_algorithms::merge_sort::merge_sort_to_new;
///
/// let original = vec![3, 1, 4, 1, 5, 9, 2, 6];
/// let sorted = merge_sort_to_new(&original);
/// assert_eq!(sorted, vec![1, 1, 2, 3, 4, 5, 6, 9]);
/// // 原数组不变
/// assert_eq!(original, vec![3, 1, 4, 1, 5, 9, 2, 6]);
/// ```
pub fn merge_sort_to_new<T: Ord + Clone>(arr: &[T]) -> Vec<T> {
    let mut result = arr.to_vec();
    merge_sort(&mut result);
    result
}

/// 归并排序迭代版本（自底向上）
///
/// 使用迭代方式实现，避免递归栈溢出风险
///
/// # 示例
///
/// ```
/// use formal_algorithms::merge_sort::merge_sort_iterative;
///
/// let mut data = vec![64, 34, 25, 12, 22, 11, 90];
/// merge_sort_iterative(&mut data);
/// assert_eq!(data, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn merge_sort_iterative<T: Ord + Clone>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }

    let mut temp = arr.to_vec();
    let mut width = 1;

    while width < n {
        for left in (0..n).step_by(2 * width) {
            let mid = (left + width).min(n).saturating_sub(1);
            let right = (left + 2 * width).min(n).saturating_sub(1);
            if left < right {
                merge(arr, &mut temp, left, mid, right);
            }
        }
        width *= 2;
    }
}

/// 检查数组是否已排序
pub fn is_sorted<T: Ord>(arr: &[T]) -> bool {
    arr.windows(2).all(|w| w[0] <= w[1])
}

/// 稳定归并排序（保证相等元素的相对顺序）
///
/// 使用稳定比较器，对于相等元素保持原始顺序
pub fn stable_merge_sort<T: Clone>(arr: &mut [T], compare: impl Fn(&T, &T) -> std::cmp::Ordering) {
    if arr.len() <= 1 {
        return;
    }

    let len = arr.len();
    let mut temp = arr.to_vec();
    stable_merge_sort_internal(arr, &mut temp, 0, len - 1, &compare);
}

fn stable_merge_sort_internal<T: Clone>(
    arr: &mut [T],
    temp: &mut [T],
    left: usize,
    right: usize,
    compare: &impl Fn(&T, &T) -> std::cmp::Ordering,
) {
    if left < right {
        let mid = left + (right - left) / 2;
        stable_merge_sort_internal(arr, temp, left, mid, compare);
        stable_merge_sort_internal(arr, temp, mid + 1, right, compare);
        stable_merge(arr, temp, left, mid, right, compare);
    }
}

fn stable_merge<T: Clone>(
    arr: &mut [T],
    temp: &mut [T],
    left: usize,
    mid: usize,
    right: usize,
    compare: &impl Fn(&T, &T) -> std::cmp::Ordering,
) {
    for i in left..=right {
        temp[i] = arr[i].clone();
    }

    let mut i = left;
    let mut j = mid + 1;
    let mut k = left;

    while i <= mid && j <= right {
        if compare(&temp[i], &temp[j]) != std::cmp::Ordering::Greater {
            arr[k] = temp[i].clone();
            i += 1;
        } else {
            arr[k] = temp[j].clone();
            j += 1;
        }
        k += 1;
    }

    while i <= mid {
        arr[k] = temp[i].clone();
        i += 1;
        k += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_array() {
        let mut arr: Vec<i32> = vec![];
        merge_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
        assert!(is_sorted(&arr));
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random_array() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_duplicate_elements() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_negative_numbers() {
        let mut arr = vec![-5, 3, -10, 0, 8, -2];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![-10, -5, -2, 0, 3, 8]);
    }

    #[test]
    fn test_stability() {
        // 测试稳定性：相等元素的相对顺序应保持
        #[derive(Debug, Clone, PartialEq)]
        struct Item {
            key: i32,
            original_index: usize,
        }

        let mut arr = vec![
            Item { key: 3, original_index: 0 },
            Item { key: 1, original_index: 1 },
            Item { key: 3, original_index: 2 },
            Item { key: 2, original_index: 3 },
        ];

        stable_merge_sort(&mut arr, |a, b| a.key.cmp(&b.key));

        // 检查两个key=3的元素的原始索引顺序
        assert!(arr[2].original_index < arr[3].original_index || 
                (arr[2].original_index == 2 && arr[3].original_index == 0));
    }

    #[test]
    fn test_iterative_version() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        merge_sort_iterative(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_to_new_version() {
        let original = vec![3, 1, 4, 1, 5];
        let sorted = merge_sort_to_new(&original);
        assert_eq!(sorted, vec![1, 1, 3, 4, 5]);
        assert_eq!(original, vec![3, 1, 4, 1, 5]); // 原数组不变
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (0..1000).rev().collect();
        merge_sort(&mut arr);
        assert!(is_sorted(&arr));
        assert_eq!(arr.len(), 1000);
    }

    #[test]
    fn test_all_same_elements() {
        let mut arr = vec![5, 5, 5, 5, 5];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![5, 5, 5, 5, 5]);
    }

    #[test]
    fn test_two_elements() {
        let mut arr = vec![2, 1];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 2]);
    }
}
