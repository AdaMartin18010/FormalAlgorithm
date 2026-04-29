// 排序算法四语言实现 - Rust版本
// 包含：快速排序、归并排序、堆排序

/// 快速排序 - 原地排序，平均O(n log n)
pub fn quick_sort<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot_index = partition(arr);
    let (left, right) = arr.split_at_mut(pivot_index);
    quick_sort(left);
    quick_sort(&mut right[1..]); // 跳过pivot
}

fn partition<T: Ord>(arr: &mut [T]) -> usize {
    let len = arr.len();
    let pivot_index = len / 2; // 选择中间元素作为pivot
    arr.swap(pivot_index, len - 1);
    
    let mut i = 0;
    for j in 0..len - 1 {
        if arr[j] <= arr[len - 1] {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, len - 1);
    i
}

/// 快速排序 - 三路划分（处理大量重复元素）
pub fn quick_sort_3way<T: Ord>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }
    
    let len = arr.len();
    arr.swap(0, len / 2); // median-of-three
    let pivot = &arr[0] as *const T;
    
    let mut lt = 0;      // arr[0..lt] < pivot
    let mut gt = len;    // arr[gt..] > pivot
    let mut i = 1;       // arr[lt..i] == pivot
    
    unsafe {
        while i < gt {
            if &arr[i] < &*pivot {
                arr.swap(lt, i);
                lt += 1;
                i += 1;
            } else if &arr[i] > &*pivot {
                gt -= 1;
                arr.swap(i, gt);
            } else {
                i += 1;
            }
        }
    }
    
    quick_sort_3way(&mut arr[..lt]);
    quick_sort_3way(&mut arr[gt..]);
}

/// 归并排序 - O(n log n)稳定排序
pub fn merge_sort<T: Ord + Clone>(arr: &[T]) -> Vec<T> {
    if arr.len() <= 1 {
        return arr.to_vec();
    }
    
    let mid = arr.len() / 2;
    let left = merge_sort(&arr[..mid]);
    let right = merge_sort(&arr[mid..]);
    
    merge(&left, &right)
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T]) -> Vec<T> {
    let mut result = Vec::with_capacity(left.len() + right.len());
    let (mut i, mut j) = (0, 0);
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result.push(left[i].clone());
            i += 1;
        } else {
            result.push(right[j].clone());
            j += 1;
        }
    }
    
    result.extend_from_slice(&left[i..]);
    result.extend_from_slice(&right[j..]);
    result
}

/// 堆排序 - 原地O(n log n)排序
pub fn heap_sort<T: Ord>(arr: &mut [T]) {
    let len = arr.len();
    if len <= 1 {
        return;
    }
    
    // 建堆（从最后一个非叶子节点开始）
    for i in (0..len / 2).rev() {
        heapify(arr, len, i);
    }
    
    // 提取元素
    for i in (1..len).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

fn heapify<T: Ord>(arr: &mut [T], heap_size: usize, root: usize) {
    let mut largest = root;
    let left = 2 * root + 1;
    let right = 2 * root + 2;
    
    if left < heap_size && arr[left] > arr[largest] {
        largest = left;
    }
    if right < heap_size && arr[right] > arr[largest] {
        largest = right;
    }
    
    if largest != root {
        arr.swap(root, largest);
        heapify(arr, heap_size, largest);
    }
}

/// 插入排序 - O(n^2)，适合小数组
pub fn insertion_sort<T: Ord>(arr: &mut [T]) {
    for i in 1..arr.len() {
        let mut j = i;
        while j > 0 && arr[j - 1] > arr[j] {
            arr.swap(j - 1, j);
            j -= 1;
        }
    }
}

/// 计数排序 - O(n + k)，适合整数
pub fn counting_sort(arr: &[usize], max_val: usize) -> Vec<usize> {
    let mut count = vec![0; max_val + 1];
    
    // 计数
    for &val in arr {
        count[val] += 1;
    }
    
    // 累加
    for i in 1..count.len() {
        count[i] += count[i - 1];
    }
    
    // 输出
    let mut output = vec![0; arr.len()];
    for &val in arr.iter().rev() {
        output[count[val] - 1] = val;
        count[val] -= 1;
    }
    
    output
}

/// 基数排序 - O(nk)，适合固定位数整数
pub fn radix_sort(arr: &mut [u32]) {
    if arr.is_empty() {
        return;
    }
    
    let max_val = *arr.iter().max().unwrap();
    let mut exp = 1;
    
    while max_val / exp > 0 {
        counting_sort_by_digit(arr, exp);
        exp *= 10;
    }
}

fn counting_sort_by_digit(arr: &mut [u32], exp: u32) {
    let len = arr.len();
    let mut output = vec![0; len];
    let mut count = [0; 10];
    
    // 按当前位计数
    for &val in arr.iter() {
        let digit = ((val / exp) % 10) as usize;
        count[digit] += 1;
    }
    
    // 累加
    for i in 1..10 {
        count[i] += count[i - 1];
    }
    
    // 输出（保持稳定）
    for &val in arr.iter().rev() {
        let digit = ((val / exp) % 10) as usize;
        output[count[digit] - 1] = val;
        count[digit] -= 1;
    }
    
    arr.copy_from_slice(&output);
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_quick_sort() {
        let mut arr = vec![3, 6, 8, 10, 1, 2, 1];
        quick_sort(&mut arr);
        assert_eq!(arr, vec![1, 1, 2, 3, 6, 8, 10]);
    }
    
    #[test]
    fn test_quick_sort_3way() {
        let mut arr = vec![3, 3, 3, 1, 1, 1, 2, 2, 2];
        quick_sort_3way(&mut arr);
        assert_eq!(arr, vec![1, 1, 1, 2, 2, 2, 3, 3, 3]);
    }
    
    #[test]
    fn test_merge_sort() {
        let arr = vec![38, 27, 43, 3, 9, 82, 10];
        let sorted = merge_sort(&arr);
        assert_eq!(sorted, vec![3, 9, 10, 27, 38, 43, 82]);
    }
    
    #[test]
    fn test_heap_sort() {
        let mut arr = vec![12, 11, 13, 5, 6, 7];
        heap_sort(&mut arr);
        assert_eq!(arr, vec![5, 6, 7, 11, 12, 13]);
    }
    
    #[test]
    fn test_counting_sort() {
        let arr = vec![4, 2, 2, 8, 3, 3, 1];
        let sorted = counting_sort(&arr, 8);
        assert_eq!(sorted, vec![1, 2, 2, 3, 3, 4, 8]);
    }
    
    #[test]
    fn test_radix_sort() {
        let mut arr = vec![170, 45, 75, 90, 802, 24, 2, 66];
        radix_sort(&mut arr);
        assert_eq!(arr, vec![2, 24, 45, 66, 75, 90, 170, 802]);
    }
}
