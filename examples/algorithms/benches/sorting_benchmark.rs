//! 排序算法性能基准测试
//! 
//! 运行方式: cargo bench --bench sorting_benchmark

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use rand::prelude::*;

/// 生成随机数组
fn generate_random_array(size: usize) -> Vec<i32> {
    let mut rng = thread_rng();
    (0..size).map(|_| rng.gen_range(0..1_000_000)).collect()
}

/// 生成有序数组（最佳情况）
fn generate_sorted_array(size: usize) -> Vec<i32> {
    (0..size as i32).collect()
}

/// 生成逆序数组（最坏情况）
fn generate_reverse_array(size: usize) -> Vec<i32> {
    (0..size as i32).rev().collect()
}

/// 生成重复元素数组
fn generate_duplicate_array(size: usize) -> Vec<i32> {
    let mut rng = thread_rng();
    (0..size).map(|_| rng.gen_range(0..100)).collect()
}

// ============== 排序算法实现 ==============

/// 冒泡排序
fn bubble_sort(arr: &mut [i32]) {
    let n = arr.len();
    for i in 0..n {
        let mut swapped = false;
        for j in 0..n - i - 1 {
            if arr[j] > arr[j + 1] {
                arr.swap(j, j + 1);
                swapped = true;
            }
        }
        if !swapped {
            break;
        }
    }
}

/// 插入排序
fn insertion_sort(arr: &mut [i32]) {
    for i in 1..arr.len() {
        let key = arr[i];
        let mut j = i;
        while j > 0 && arr[j - 1] > key {
            arr[j] = arr[j - 1];
            j -= 1;
        }
        arr[j] = key;
    }
}

/// 选择排序
fn selection_sort(arr: &mut [i32]) {
    let n = arr.len();
    for i in 0..n {
        let mut min_idx = i;
        for j in i + 1..n {
            if arr[j] < arr[min_idx] {
                min_idx = j;
            }
        }
        arr.swap(i, min_idx);
    }
}

/// 归并排序
fn merge_sort(arr: &mut [i32]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    let mid = n / 2;
    merge_sort(&mut arr[..mid]);
    merge_sort(&mut arr[mid..]);
    
    let mut temp = arr.to_vec();
    let (left, right) = arr.split_at_mut(mid);
    
    let mut i = 0;
    let mut j = 0;
    let mut k = 0;
    
    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            temp[k] = left[i];
            i += 1;
        } else {
            temp[k] = right[j];
            j += 1;
        }
        k += 1;
    }
    
    while i < left.len() {
        temp[k] = left[i];
        i += 1;
        k += 1;
    }
    
    while j < right.len() {
        temp[k] = right[j];
        j += 1;
        k += 1;
    }
    
    arr.copy_from_slice(&temp);
}

/// 快速排序
fn quick_sort(arr: &mut [i32]) {
    if arr.len() <= 1 {
        return;
    }
    let pivot_idx = partition(arr);
    let (left, right) = arr.split_at_mut(pivot_idx);
    quick_sort(left);
    quick_sort(&mut right[1..]);
}

fn partition(arr: &mut [i32]) -> usize {
    let n = arr.len();
    let pivot = arr[n - 1];
    let mut i = 0;
    
    for j in 0..n - 1 {
        if arr[j] <= pivot {
            arr.swap(i, j);
            i += 1;
        }
    }
    arr.swap(i, n - 1);
    i
}

/// 堆排序
fn heap_sort(arr: &mut [i32]) {
    let n = arr.len();
    
    // 建堆
    for i in (0..n / 2).rev() {
        heapify(arr, n, i);
    }
    
    // 排序
    for i in (1..n).rev() {
        arr.swap(0, i);
        heapify(arr, i, 0);
    }
}

fn heapify(arr: &mut [i32], n: usize, mut i: usize) {
    loop {
        let left = 2 * i + 1;
        let right = 2 * i + 2;
        let mut largest = i;
        
        if left < n && arr[left] > arr[largest] {
            largest = left;
        }
        if right < n && arr[right] > arr[largest] {
            largest = right;
        }
        
        if largest == i {
            break;
        }
        
        arr.swap(i, largest);
        i = largest;
    }
}

// ============== 基准测试 ==============

fn bench_sorting_algorithms(c: &mut Criterion) {
    let mut group = c.benchmark_group("Sorting Algorithms");
    
    // 测试不同规模的随机数组
    for size in [100, 1_000, 10_000].iter() {
        let input = generate_random_array(*size);
        
        group.bench_with_input(
            BenchmarkId::new("Bubble Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    bubble_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Insertion Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    insertion_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Selection Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    selection_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Merge Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    merge_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Quick Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    quick_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Heap Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    heap_sort(black_box(&mut arr));
                });
            },
        );
        
        // 对比标准库排序
        group.bench_with_input(
            BenchmarkId::new("Std Sort (unstable)", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    arr.sort_unstable();
                    black_box(arr);
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Std Sort (stable)", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    arr.sort();
                    black_box(arr);
                });
            },
        );
    }
    
    group.finish();
}

fn bench_different_data_patterns(c: &mut Criterion) {
    let mut group = c.benchmark_group("Data Patterns (n=10000)");
    let size = 10_000;
    
    let patterns = [
        ("Random", generate_random_array(size)),
        ("Sorted", generate_sorted_array(size)),
        ("Reverse", generate_reverse_array(size)),
        ("Duplicate", generate_duplicate_array(size)),
    ];
    
    for (name, data) in patterns.iter() {
        group.bench_with_input(
            BenchmarkId::new("Quick Sort", name),
            name,
            |b, _| {
                b.iter(|| {
                    let mut arr = data.clone();
                    quick_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Merge Sort", name),
            name,
            |b, _| {
                b.iter(|| {
                    let mut arr = data.clone();
                    merge_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Insertion Sort", name),
            name,
            |b, _| {
                b.iter(|| {
                    let mut arr = data.clone();
                    insertion_sort(black_box(&mut arr));
                });
            },
        );
    }
    
    group.finish();
}

fn bench_small_arrays(c: &mut Criterion) {
    let mut group = c.benchmark_group("Small Arrays");
    
    for size in [10, 20, 50].iter() {
        let input = generate_random_array(*size);
        
        group.bench_with_input(
            BenchmarkId::new("Insertion Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    insertion_sort(black_box(&mut arr));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Quick Sort", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut arr = input.clone();
                    quick_sort(black_box(&mut arr));
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_sorting_algorithms,
    bench_different_data_patterns,
    bench_small_arrays
);
criterion_main!(benches);

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_all_sorts() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        let expected = vec![11, 12, 22, 25, 34, 64, 90];
        
        let mut test_arr = arr.clone();
        bubble_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
        
        test_arr = arr.clone();
        insertion_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
        
        test_arr = arr.clone();
        selection_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
        
        test_arr = arr.clone();
        merge_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
        
        test_arr = arr.clone();
        quick_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
        
        test_arr = arr.clone();
        heap_sort(&mut test_arr);
        assert_eq!(test_arr, expected);
    }
}
