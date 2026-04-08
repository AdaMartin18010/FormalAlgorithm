//! 堆排序实现
//!
//! 堆排序是一种基于二叉堆数据结构的比较排序算法。
//! 它利用堆的性质，通过反复提取最大（或最小）元素来实现排序。

use crate::{AlgorithmError, SearchResult};
use std::cmp::Ordering;

/// 对可变切片进行堆排序
///
/// # 算法说明
///
/// 堆排序分为两个阶段：
/// 1. **建堆**：将无序数组构建成最大堆
/// 2. **排序**：反复将堆顶元素（最大值）移到数组末尾，然后调整堆
///
/// 堆的性质：对于索引 i，左子节点为 2i+1，右子节点为 2i+2，父节点为 (i-1)/2
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n log n)
///   - 建堆：O(n)
///   - 每次提取最大元素：O(log n)
///   - 共 n 次提取：O(n log n)
/// - **空间复杂度**：O(1) - 原地排序
/// - **稳定性**：不稳定排序
///
/// # 示例
///
/// ```
/// use formal_algorithms::heap_sort;
///
/// let mut data = vec![12, 11, 13, 5, 6, 7];
/// heap_sort(&mut data);
/// assert_eq!(data, vec![5, 6, 7, 11, 12, 13]);
/// ```
///
/// # 类型参数
///
/// * `T` - 必须实现 `Ord` trait 的类型
pub fn heap_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();

    // 建堆：从最后一个非叶子节点开始，自下而上调整
    for i in (0..n / 2).rev() {
        heapify(arr, n, i);
    }

    // 排序：将堆顶移到末尾，然后调整剩余部分
    for i in (1..n).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

/// 调整堆，使以 root 为根的子树满足最大堆性质
///
/// # 参数
///
/// * `arr` - 数组
/// * `heap_size` - 堆的大小
/// * `root` - 根节点索引
fn heapify<T: Ord>(arr: &mut [T], heap_size: usize, root: usize) {
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;

    // 找出 root、left、right 中的最大值
    if left < heap_size && arr[left] > arr[largest] {
        largest = left;
    }
    if right < heap_size && arr[right] > arr[largest] {
        largest = right;
    }

    // 如果最大值不是 root，交换并继续调整
    if largest != root {
        arr.swap(root, largest);
        heapify(arr, heap_size, largest);
    }
}

/// 最小堆排序（升序排列，使用最小堆）
///
/// 与最大堆版本功能相同，只是实现方式不同
///
/// # 示例
///
/// ```
/// use formal_algorithms::heap_sort::heap_sort_min;
///
/// let mut data = vec![12, 11, 13, 5, 6, 7];
/// heap_sort_min(&mut data);
/// assert_eq!(data, vec![5, 6, 7, 11, 12, 13]);
/// ```
pub fn heap_sort_min<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    // 构建最小堆
    build_min_heap(arr);

    // 提取元素
    let n = arr.len();
    for i in 0..n {
        // 将堆顶（最小值）与当前位置交换
        arr.swap(0, n - 1 - i);
        // 调整剩余元素
        min_heapify(&mut arr[..n - 1 - i], 0);
    }
}

fn build_min_heap<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    for i in (0..n / 2).rev() {
        min_heapify(arr, i);
    }
}

fn min_heapify<T: Ord>(arr: &mut [T], root: usize) {
    let n = arr.len();
    let mut smallest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;

    if left < n && arr[left] < arr[smallest] {
        smallest = left;
    }
    if right < n && arr[right] < arr[smallest] {
        smallest = right;
    }

    if smallest != root {
        arr.swap(root, smallest);
        min_heapify(arr, smallest);
    }
}

/// 泛型堆排序（支持自定义比较器）
///
/// 使用比较器函数定义元素顺序
///
/// # 示例
///
/// ```
/// use formal_algorithms::heap_sort::heap_sort_by;
///
/// let mut data = vec![3, 1, 4, 1, 5, 9, 2, 6];
/// heap_sort_by(&mut data, |a, b| a.cmp(b));
/// assert_eq!(data, vec![1, 1, 2, 3, 4, 5, 6, 9]);
///
/// // 降序排序
/// heap_sort_by(&mut data, |a, b| b.cmp(a));
/// assert_eq!(data, vec![9, 6, 5, 4, 3, 2, 1, 1]);
/// ```
pub fn heap_sort_by<T, F>(arr: &mut [T], mut compare: F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();

    // 建堆
    for i in (0..n / 2).rev() {
        heapify_by(arr, n, i, &mut compare);
    }

    // 排序
    for i in (1..n).rev() {
        arr.swap(0, i);
        heapify_by(arr, i, 0, &mut compare);
    }
}

fn heapify_by<T, F>(arr: &mut [T], heap_size: usize, root: usize, compare: &mut F)
where
    F: FnMut(&T, &T) -> Ordering,
{
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;

    if left < heap_size && compare(&arr[left], &arr[largest]) == Ordering::Greater {
        largest = left;
    }
    if right < heap_size && compare(&arr[right], &arr[largest]) == Ordering::Greater {
        largest = right;
    }

    if largest != root {
        arr.swap(root, largest);
        heapify_by(arr, heap_size, largest, compare);
    }
}

/// 迭代版本的堆化（避免递归栈溢出）
///
/// 适用于非常大的数组
///
/// # 示例
///
/// ```
/// use formal_algorithms::heap_sort::heap_sort_iterative;
///
/// let mut data = vec![12, 11, 13, 5, 6, 7];
/// heap_sort_iterative(&mut data);
/// assert_eq!(data, vec![5, 6, 7, 11, 12, 13]);
/// ```
pub fn heap_sort_iterative<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();

    // 建堆
    for i in (0..n / 2).rev() {
        heapify_iterative(arr, n, i);
    }

    // 排序
    for i in (1..n).rev() {
        arr.swap(0, i);
        heapify_iterative(arr, i, 0);
    }
}

fn heapify_iterative<T: Ord>(arr: &mut [T], heap_size: usize, mut root: usize) {
    loop {
        let mut largest = root;
        let left = 2 * root + 1;
        let right = 2 * root + 2;

        if left < heap_size && arr[left] > arr[largest] {
            largest = left;
        }
        if right < heap_size && arr[right] > arr[largest] {
            largest = right;
        }

        if largest == root {
            break;
        }

        arr.swap(root, largest);
        root = largest;
    }
}

/// 检查数组是否满足最大堆性质
///
/// 用于调试和测试
pub fn is_max_heap<T: Ord>(arr: &[T]) -> bool {
    let n = arr.len();
    for i in 0..n / 2 {
        let left = 2 * i + 1;
        let right = 2 * i + 2;

        if left < n && arr[i] < arr[left] {
            return false;
        }
        if right < n && arr[i] < arr[right] {
            return false;
        }
    }
    true
}

/// 检查数组是否已排序
pub fn is_sorted<T: Ord>(arr: &[T]) -> bool {
    arr.windows(2).all(|w| w[0] <= w[1])
}

/// Floyd建堆算法
///
/// 优化的建堆方法，时间复杂度仍为 O(n)，但常数更小
pub fn heap_sort_floyd<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let n = arr.len();

    // Floyd建堆
    for i in (0..n / 2).rev() {
        sift_down(arr, n, i);
    }

    // 排序
    for i in (1..n).rev() {
        arr.swap(0, i);
        sift_down(arr, i, 0);
    }
}

/// 下沉操作（Floyd算法）
fn sift_down<T: Ord>(arr: &mut [T], heap_size: usize, mut root: usize) {
    let value = std::ptr::addr_of!(arr[root]);
    
    loop {
        let left = 2 * root + 1;
        if left >= heap_size {
            break;
        }

        let right = left + 1;
        let mut largest = if right < heap_size && arr[right] > arr[left] {
            right
        } else {
            left
        };

        // 安全比较
        if arr[largest] <= arr[root] {
            break;
        }

        arr.swap(root, largest);
        root = largest;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_array() {
        let mut arr: Vec<i32> = vec![];
        heap_sort(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_single_element() {
        let mut arr = vec![42];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![42]);
    }

    #[test]
    fn test_already_sorted() {
        let mut arr = vec![1, 2, 3, 4, 5];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_reverse_sorted() {
        let mut arr = vec![5, 4, 3, 2, 1];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![1, 2, 3, 4, 5]);
    }

    #[test]
    fn test_random_array() {
        let mut arr = vec![12, 11, 13, 5, 6, 7];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![5, 6, 7, 11, 12, 13]);
    }

    #[test]
    fn test_duplicate_elements() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 3, 4, 5, 5, 6, 9]);
    }

    #[test]
    fn test_min_heap_sort() {
        let mut arr = vec![12, 11, 13, 5, 6, 7];
        heap_sort_min(&mut arr);
        assert_eq!(arr, vec![5, 6, 7, 11, 12, 13]);
    }

    #[test]
    fn test_heap_sort_by() {
        let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        
        // 升序
        heap_sort_by(&mut arr, |a, b| a.cmp(b));
        assert_eq!(arr, vec![1, 1, 2, 3, 4, 5, 6, 9]);
        
        // 降序
        heap_sort_by(&mut arr, |a, b| b.cmp(a));
        assert_eq!(arr, vec![9, 6, 5, 4, 3, 2, 1, 1]);
    }

    #[test]
    fn test_heap_sort_iterative() {
        let mut arr = vec![12, 11, 13, 5, 6, 7];
        heap_sort_iterative(&mut arr);
        assert_eq!(arr, vec![5, 6, 7, 11, 12, 13]);
    }

    #[test]
    fn test_is_max_heap() {
        let heap = vec![9, 8, 7, 6, 5, 4, 3];
        assert!(is_max_heap(&heap));

        let not_heap = vec![1, 2, 3];
        assert!(!is_max_heap(&not_heap));
    }

    #[test]
    fn test_large_array() {
        let mut arr: Vec<i32> = (0..1000).rev().collect();
        heap_sort(&mut arr);
        assert!(is_sorted(&arr));
    }

    #[test]
    fn test_heap_sort_floyd() {
        let mut arr = vec![12, 11, 13, 5, 6, 7];
        heap_sort_floyd(&mut arr);
        assert_eq!(arr, vec![5, 6, 7, 11, 12, 13]);
    }

    #[test]
    fn test_all_same_elements() {
        let mut arr = vec![5, 5, 5, 5, 5];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![5, 5, 5, 5, 5]);
    }

    #[test]
    fn test_two_elements() {
        let mut arr = vec![2, 1];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![1, 2]);
    }

    #[test]
    fn test_struct_sorting() {
        #[derive(Debug, Clone, PartialEq)]
        struct Item {
            key: i32,
            value: String,
        }

        impl PartialOrd for Item {
            fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
                self.key.partial_cmp(&other.key)
            }
        }

        impl Ord for Item {
            fn cmp(&self, other: &Self) -> Ordering {
                self.key.cmp(&other.key)
            }
        }

        impl Eq for Item {}

        let mut arr = vec![
            Item { key: 3, value: "c".to_string() },
            Item { key: 1, value: "a".to_string() },
            Item { key: 2, value: "b".to_string() },
        ];

        heap_sort(&mut arr);
        
        assert_eq!(arr[0].key, 1);
        assert_eq!(arr[1].key, 2);
        assert_eq!(arr[2].key, 3);
    }
}
