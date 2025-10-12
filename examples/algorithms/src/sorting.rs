//! # 排序算法 / Sorting Algorithms
//!
//! 实现经典排序算法及其形式化规范。
//!
//! Implements classic sorting algorithms with formal specifications.

/// 归并排序 / Merge Sort
///
/// # 形式化定义 / Formal Definition
///
/// 归并排序是基于分治策略的排序算法：
/// 1. **分解（Divide）**: 将数组分成两半
/// 2. **递归（Conquer）**: 递归排序两个子数组
/// 3. **合并（Combine）**: 合并两个已排序的子数组
///
/// ## 时间复杂度 / Time Complexity
/// - 最好情况: O(n log n)
/// - 平均情况: O(n log n)
/// - 最坏情况: O(n log n)
///
/// ## 空间复杂度 / Space Complexity
/// - O(n) - 需要额外空间存储临时数组
///
/// ## 稳定性 / Stability
/// - 稳定排序（保持相等元素的相对顺序）
///
/// # 参考文献 / References
/// - [CLRS2009] Cormen et al., "Introduction to Algorithms", 第3版, 第2.3节
/// - 对应文档: `docs/09-算法理论/02-算法设计范式/01-分治策略.md`
///
/// # Examples
///
/// ```
/// use algorithms::sorting::merge_sort;
///
/// let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
/// merge_sort(&mut arr);
/// assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn merge_sort<T: Ord + Clone>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    
    let mid = len / 2;
    
    // 递归排序左半部分
    merge_sort(&mut arr[..mid]);
    
    // 递归排序右半部分
    merge_sort(&mut arr[mid..]);
    
    // 合并两个已排序的部分
    merge(arr, mid);
}

/// 合并两个已排序的子数组
///
/// # 不变量 / Invariant
/// - arr[0..mid] 已排序
/// - arr[mid..len] 已排序
/// - 合并后 arr[0..len] 已排序
fn merge<T: Ord + Clone>(arr: &mut [T], mid: usize) {
    let left = arr[..mid].to_vec();
    let right = arr[mid..].to_vec();
    
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    
    // 归并过程
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            arr[k] = left[i].clone();
            i += 1;
        } else {
            arr[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }
    
    // 复制剩余元素
    while i < left.len() {
        arr[k] = left[i].clone();
        i += 1;
        k += 1;
    }
    
    while j < right.len() {
        arr[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}

/// 快速排序 / Quick Sort
///
/// # 形式化定义 / Formal Definition
///
/// 快速排序也是基于分治策略，但采用不同的分解方法：
/// 1. **选择枢轴（Pivot）**: 选择一个元素作为枢轴
/// 2. **分区（Partition）**: 重排数组，使得小于枢轴的元素在左边，大于的在右边
/// 3. **递归排序**: 递归排序左右两个分区
///
/// ## 时间复杂度 / Time Complexity
/// - 最好情况: O(n log n) - 每次分区都平衡
/// - 平均情况: O(n log n)
/// - 最坏情况: O(n²) - 每次选择的枢轴都是最大或最小元素
///
/// ## 空间复杂度 / Space Complexity
/// - O(log n) - 递归调用栈
///
/// ## 稳定性 / Stability
/// - 不稳定排序
///
/// # 参考文献 / References
/// - [CLRS2009] Cormen et al., "Introduction to Algorithms", 第3版, 第7章
/// - 对应文档: `docs/09-算法理论/02-算法设计范式/01-分治策略.md`
///
/// # Examples
///
/// ```
/// use algorithms::sorting::quick_sort;
///
/// let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
/// quick_sort(&mut arr);
/// assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn quick_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    
    quick_sort_helper(arr, 0, len - 1);
}

fn quick_sort_helper<T: Ord>(arr: &mut [T], low: usize, high: usize) {
    if low < high {
        let pivot_index = partition(arr, low, high);
        
        // 递归排序左半部分
        if pivot_index > 0 {
            quick_sort_helper(arr, low, pivot_index - 1);
        }
        
        // 递归排序右半部分
        quick_sort_helper(arr, pivot_index + 1, high);
    }
}

/// 分区函数
///
/// # 不变量 / Invariant
/// - arr[low..i] < pivot
/// - arr[i+1..high] >= pivot
/// - 返回枢轴的最终位置
fn partition<T: Ord>(arr: &mut [T], low: usize, high: usize) -> usize {
    let pivot_index = high;
    let mut i = low;
    
    for j in low..high {
        if arr[j] < arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }
    
    arr.swap(i, pivot_index);
    i
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_merge_sort_basic() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }
    
    #[test]
    fn test_merge_sort_empty() {
        let mut arr: Vec<i32> = vec![];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![]);
    }
    
    #[test]
    fn test_merge_sort_single() {
        let mut arr = vec![42];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }
    
    #[test]
    fn test_merge_sort_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }
    
    #[test]
    fn test_merge_sort_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        merge_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }
    
    #[test]
    fn test_quick_sort_basic() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }
    
    #[test]
    fn test_quick_sort_empty() {
        let mut arr: Vec<i32> = vec![];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![]);
    }
    
    #[test]
    fn test_quick_sort_single() {
        let mut arr = vec![42];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }
    
    #[test]
    fn test_quick_sort_duplicates() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 5, 6, 9]);
    }
    
    #[test]
    fn test_sort_strings() {
        let mut arr = vec!["dog", "cat", "bird", "ant"];
        merge_sort(&mut arr);
        assert_eq!(arr, vec!["ant", "bird", "cat", "dog"]);
        
        let mut arr2 = vec!["dog", "cat", "bird", "ant"];
        quick_sort(&mut arr2);
        assert_eq!(arr2, vec!["ant", "bird", "cat", "dog"]);
    }
}

#[cfg(test)]
mod property_tests {
    use super::*;
    use proptest::prelude::*;
    
    proptest! {
        #[test]
        fn test_merge_sort_is_sorted(vec in prop::collection::vec(any::<i32>(), 0..100)) {
            let mut sorted = vec.clone();
            merge_sort(&mut sorted);
            
            // 验证已排序
            for i in 1..sorted.len() {
                assert!(sorted[i-1] <= sorted[i]);
            }
        }
        
        #[test]
        fn test_merge_sort_has_same_elements(vec in prop::collection::vec(any::<i32>(), 0..100)) {
            let mut sorted = vec.clone();
            merge_sort(&mut sorted);
            
            // 验证元素数量相同
            assert_eq!(vec.len(), sorted.len());
            
            // 验证包含相同元素（通过排序后比较）
            let mut original_sorted = vec.clone();
            original_sorted.sort();
            assert_eq!(original_sorted, sorted);
        }
        
        #[test]
        fn test_quick_sort_is_sorted(vec in prop::collection::vec(any::<i32>(), 0..100)) {
            let mut sorted = vec.clone();
            quick_sort(&mut sorted);
            
            for i in 1..sorted.len() {
                assert!(sorted[i-1] <= sorted[i]);
            }
        }
    }
}

