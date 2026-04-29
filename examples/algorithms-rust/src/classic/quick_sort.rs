//! 快速排序实现
//!
//! 快速排序是一种基于分治策略的高效排序算法。
//! 它选择一个"基准"元素，将数组分区后递归排序。

use crate::{AlgorithmError, SearchResult};

/// 对可变切片进行快速排序
///
/// # 算法说明
///
/// 快速排序采用分治法(Divide and Conquer)策略：
/// 1. **选择基准**：从数组中选择一个元素作为基准(pivot)
/// 2. **分区**：将数组分为两部分，小于基准的放左边，大于基准的放右边
/// 3. **递归排序**：对左右两部分递归地进行快速排序
///
/// 本实现采用三数取中法选择基准，避免最坏情况。
///
/// # 复杂度分析
///
/// - **时间复杂度**：
///   - 最好情况：O(n log n) - 每次分区平衡
///   - 最坏情况：O(n²) - 每次分区极不平衡
///   - 平均情况：O(n log n)
/// - **空间复杂度**：O(log n) - 递归栈空间
/// - **稳定性**：不稳定排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_sort;
///
/// let mut data = vec![10, 7, 8, 9, 1, 5];
/// quick_sort(&mut data);
/// assert_eq!(data, vec![1, 5, 7, 8, 9, 10]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let len = arr.len();
    quick_sort_internal(arr, 0, len - 1);
}

/// 内部递归函数
fn quick_sort_internal<T: Ord>(arr: &mut [T], low: usize, high: usize) {
    if low < high {
        let pivot_index = partition(arr, low, high);
        if pivot_index > 0 {
            quick_sort_internal(arr, low, pivot_index - 1);
        }
        quick_sort_internal(arr, pivot_index + 1, high);
    }
}

/// Lomuto分区方案
///
/// 选择最后一个元素作为基准，返回基准最终位置
fn partition<T: Ord>(arr: &mut [T], low: usize, high: usize) -> usize {
    // 三数取中优化
    let mid = low + (high - low) / 2;
    
    // 将中位数放到high位置
    if arr[mid] < arr[low] {
        arr.swap(low, mid);
    }
    if arr[high] < arr[low] {
        arr.swap(low, high);
    }
    if arr[mid] < arr[high] {
        arr.swap(mid, high);
    }

    let pivot_index = high;
    let mut i = low;

    for j in low..high {
        if arr[j] < arr[pivot_index] {
            arr.swap(i, j);
            i += 1;
        }
    }

    arr.swap(i, high);
    i
}

/// Hoare分区方案（更高效的分区方式）
///
/// 返回分区点，左边<=基准，右边>=基准
fn hoare_partition<T: Ord>(arr: &mut [T], low: usize, high: usize) -> usize {
    let pivot_index = low + (high - low) / 2;
    arr.swap(low, pivot_index);
    let mut i = low as isize;
    let mut j = high as isize + 1;

    loop {
        loop {
            i += 1;
            if i > high as isize || arr[i as usize] >= arr[low] {
                break;
            }
        }
        loop {
            j -= 1;
            if arr[j as usize] <= arr[low] {
                break;
            }
        }
        if i >= j {
            arr.swap(low, j as usize);
            return j as usize;
        }
        arr.swap(i as usize, j as usize);
    }
}

/// 使用Hoare分区的快速排序
///
/// 通常比Lomuto分区更高效
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_sort::quick_sort_hoare;
///
/// let mut data = vec![10, 7, 8, 9, 1, 5];
/// quick_sort_hoare(&mut data);
/// assert_eq!(data, vec![1, 5, 7, 8, 9, 10]);
/// ```
pub fn quick_sort_hoare<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let len = arr.len();
    quick_sort_hoare_internal(arr, 0, len - 1);
}

fn quick_sort_hoare_internal<T: Ord>(arr: &mut [T], low: usize, high: usize) {
    if low < high {
        let pivot_index = hoare_partition(arr, low, high);
        quick_sort_hoare_internal(arr, low, pivot_index);
        quick_sort_hoare_internal(arr, pivot_index + 1, high);
    }
}

/// 三路快速排序（处理大量重复元素）
///
/// 将数组分为三部分：小于、等于、大于基准
/// 对于有大量重复元素的数组，性能接近O(n)
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_sort::quick_sort_3way;
///
/// let mut data = vec![2, 3, 1, 2, 3, 2, 1, 1, 3];
/// quick_sort_3way(&mut data);
/// assert_eq!(data, vec![1, 1, 1, 2, 2, 2, 3, 3, 3]);
/// ```
pub fn quick_sort_3way<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let len = arr.len();
    quick_sort_3way_internal(arr, 0, len - 1);
}

fn quick_sort_3way_internal<T: Ord + Clone>(arr: &mut [T], low: usize, high: usize) {
    if low >= high {
        return;
    }

    let (lt, gt) = partition_3way(arr, low, high);
    
    if lt > 0 {
        quick_sort_3way_internal(arr, low, lt - 1);
    }
    if gt < high {
        quick_sort_3way_internal(arr, gt + 1, high);
    }
}

/// 三路分区
///
/// 返回 (lt, gt)，其中：
/// - arr[low..lt] < pivot
/// - arr[lt..=gt] == pivot
/// - arr[gt+1..=high] > pivot
fn partition_3way<T: Ord + Clone>(arr: &mut [T], low: usize, high: usize) -> (usize, usize) {
    // 使用最后一个元素作为pivot（简化实现）
    let pivot = arr[high].clone();
    let mut lt = low;      // arr[low..lt] < pivot
    let mut gt = high;     // arr[gt..=high] > pivot
    let mut i = low;       // 当前扫描位置

    while i <= gt {
        if arr[i] < pivot {
            arr.swap(lt, i);
            lt += 1;
            i += 1;
        } else if arr[i] > pivot {
            arr.swap(i, gt);
            if gt == 0 { break; }
            gt -= 1;
        } else {
            i += 1;
        }
    }
    
    (lt, gt)
}

/// 尾递归优化的快速排序
///
/// 减少递归深度，避免栈溢出
pub fn quick_sort_tail_recursive<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let mut stack = vec![(0, arr.len() - 1)];
    
    while let Some((low, high)) = stack.pop() {
        if low < high {
            let pivot = partition(arr, low, high);
            
            // 先处理较小的分区，减少栈深度
            let left_size = if pivot > 0 { pivot - low } else { 0 };
            let right_size = high - pivot;
            
            if left_size < right_size {
                if pivot > 0 {
                    stack.push((low, pivot - 1));
                }
                stack.push((pivot + 1, high));
            } else {
                stack.push((pivot + 1, high));
                if pivot > 0 {
                    stack.push((low, pivot - 1));
                }
            }
        }
    }
}

/// 内省排序（Introspective Sort）
///
/// 结合快速排序、堆排序和插入排序
/// - 小数组使用插入排序
/// - 递归深度过大时切换为堆排序
/// - 一般情况下使用快速排序
///
/// 这是C++ std::sort的实现方式
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_sort::intro_sort;
///
/// let mut data = vec![10, 7, 8, 9, 1, 5, 100, 50, 25];
/// intro_sort(&mut data);
/// assert_eq!(data, vec![1, 5, 7, 8, 9, 10, 25, 50, 100]);
/// ```
pub fn intro_sort<T: Ord>(arr: &mut [T]) {
    let max_depth = (arr.len() as f64).log2() as usize * 2;
    intro_sort_internal(arr, 0, arr.len().saturating_sub(1), max_depth);
}

fn intro_sort_internal<T: Ord>(arr: &mut [T], low: usize, high: usize, depth_limit: usize) {
    const INSERTION_THRESHOLD: usize = 16;
    
    if high <= low {
        return;
    }
    
    if high - low + 1 <= INSERTION_THRESHOLD {
        insertion_sort(&mut arr[low..=high]);
        return;
    }
    
    if depth_limit == 0 {
        // 使用堆排序
        super::heap_sort::heap_sort(&mut arr[low..=high]);
        return;
    }
    
    let pivot = partition(arr, low, high);
    
    if pivot > 0 {
        intro_sort_internal(arr, low, pivot - 1, depth_limit - 1);
    }
    intro_sort_internal(arr, pivot + 1, high, depth_limit - 1);
}

/// 插入排序（用于小数组优化）
fn insertion_sort<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j] < arr[j - 1] {
            arr.swap(j, j - 1);
            j -= 1;
        }
    }
}

/// 检查数组是否已排序
pub fn is_sorted<T: Ord>(arr: &[T]) -> bool {
    arr.windows(2).all(|w| w[0] <= w[1])
}

/// 选择第k小的元素（Quick Select）
///
/// 平均时间复杂度 O(n)，用于查找中位数等场景
///
/// # 示例
///
/// ```
/// use formal_algorithms::quick_sort::quick_select;
///
/// let mut data = vec![7, 10, 4, 3, 20, 15];
/// let kth = quick_select(&mut data, 3).unwrap(); // 第4小的元素（0索引）
/// assert_eq!(kth, 10);
/// ```
pub fn quick_select<T: Ord + Clone>(arr: &mut [T], k: usize) -> SearchResult<T> {
    if k >= arr.len() {
        return Err(AlgorithmError::IndexOutOfBounds {
            index: k,
            len: arr.len(),
        });
    }
    
    let result = quick_select_internal(arr, 0, arr.len() - 1, k);
    Ok(result.clone())
}

fn quick_select_internal<T: Ord>(arr: &mut [T], low: usize, high: usize, k: usize) -> &T {
    if low == high {
        return &arr[low];
    }
    
    let pivot_index = partition(arr, low, high);
    
    match k.cmp(&pivot_index) {
        std::cmp::Ordering::Equal => &arr[pivot_index],
        std::cmp::Ordering::Less => {
            if pivot_index > 0 {
                quick_select_internal(arr, low, pivot_index - 1, k)
            } else {
                &arr[0]
            }
        }
        std::cmp::Ordering::Greater => {
            quick_select_internal(arr, pivot_index + 1, high, k)
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_array() {
        let mut arr: Vec<i32> = vec![];
        quick_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random_array() {
        let mut arr = vec![10, 7, 8, 9, 1, 5];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 5, 7, 8, 9, 10]);
    }

    #[test]
    fn test_duplicate_elements() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (0..1000).rev().collect();
        quick_sort(&mut arr);
        assert!(is_sorted(&arr));
    }

    #[test]
    fn test_hoare_partition() {
        let mut arr = vec![10, 7, 8, 9, 1, 5];
        quick_sort_hoare(&mut arr);
        assert_eq!(arr, vec![1, 5, 7, 8, 9, 10]);
    }

    #[test]
    fn test_3way_sort() {
        let mut arr = vec![2, 3, 1, 2, 3, 2, 1, 1, 3];
        quick_sort_3way(&mut arr);
        assert_eq!(arr, vec![1, 1, 1, 2, 2, 2, 3, 3, 3]);
    }

    #[test]
    fn test_intro_sort() {
        let mut arr = vec![10, 7, 8, 9, 1, 5, 100, 50, 25];
        intro_sort(&mut arr);
        assert_eq!(arr, vec![1, 5, 7, 8, 9, 10, 25, 50, 100]);
    }

    #[test]
    fn test_quick_select() {
        let mut arr = vec![7, 10, 4, 3, 20, 15];
        assert_eq!(quick_select(&mut arr, 0).unwrap(), 3);  // 最小
        assert_eq!(quick_select(&mut arr, 2).unwrap(), 7);  // 第3小
        assert_eq!(quick_select(&mut arr, 5).unwrap(), 20); // 最大
    }

    #[test]
    fn test_quick_select_error() {
        let mut arr = vec![1, 2, 3];
        assert!(quick_select(&mut arr, 10).is_err());
    }

    #[test]
    fn test_all_same_elements() {
        let mut arr = vec![5, 5, 5, 5, 5];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![5, 5, 5, 5, 5]);
    }

    #[test]
    fn test_string_sorting() {
        let mut arr = vec!["banana", "apple", "cherry", "date"];
        quick_sort(&mut arr);
        assert_eq!(arr, vec!["apple", "banana", "cherry", "date"]);
    }
}
