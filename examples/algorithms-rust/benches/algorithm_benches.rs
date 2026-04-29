//! 算法性能基准测试
//!
//! 使用 criterion.rs 对10个核心算法进行性能测试

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use formal_algorithms::*;
use std::collections::HashMap;

// ========== 排序算法基准测试 ==========

fn bench_sorting(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting");

    // 测试不同大小的数组
    for size in [100, 1000, 10000].iter() {
        // 随机数据
        let random_data: Vec<i32> = (0..*size).map(|i| (i * 17 + 31) % *size as i32).collect();
        
        // 已排序数据
        let sorted_data: Vec<i32> = (0..*size as i32).collect();
        
        // 逆序数据
        let reverse_data: Vec<i32> = (0..*size as i32).rev().collect();

        // 归并排序 - 随机数据
        group.bench_with_input(
            BenchmarkId::new("merge_sort_random", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut data = random_data.clone();
                    merge_sort(black_box(&mut data));
                });
            },
        );

        // 快速排序 - 随机数据
        group.bench_with_input(
            BenchmarkId::new("quick_sort_random", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut data = random_data.clone();
                    quick_sort(black_box(&mut data));
                });
            },
        );

        // 堆排序 - 随机数据
        group.bench_with_input(
            BenchmarkId::new("heap_sort_random", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut data = random_data.clone();
                    heap_sort(black_box(&mut data));
                });
            },
        );

        // 快速排序 - 已排序数据（测试最坏情况）
        group.bench_with_input(
            BenchmarkId::new("quick_sort_sorted", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut data = sorted_data.clone();
                    quick_sort(black_box(&mut data));
                });
            },
        );

        // 堆排序 - 已排序数据
        group.bench_with_input(
            BenchmarkId::new("heap_sort_sorted", size),
            size,
            |b, _| {
                b.iter(|| {
                    let mut data = sorted_data.clone();
                    heap_sort(black_box(&mut data));
                });
            },
        );
    }

    group.finish();
}

// ========== 搜索算法基准测试 ==========

fn bench_searching(c: &mut Criterion) {
    let mut group = c.benchmark_group("searching");

    for size in [100, 1000, 10000, 100000].iter() {
        let data: Vec<i32> = (0..*size as i32).collect();
        let target = (*size / 2) as i32;

        // 二分搜索 - 存在
        group.bench_with_input(
            BenchmarkId::new("binary_search_hit", size),
            size,
            |b, _| {
                b.iter(|| {
                    binary_search(black_box(&data), black_box(target));
                });
            },
        );

        // 二分搜索 - 不存在
        group.bench_with_input(
            BenchmarkId::new("binary_search_miss", size),
            size,
            |b, _| {
                b.iter(|| {
                    binary_search(black_box(&data), black_box(-1));
                });
            },
        );
    }

    group.finish();
}

// ========== 图算法基准测试 ==========

fn bench_graph(c: &mut Criterion) {
    let mut group = c.benchmark_group("graph");

    // BFS
    for size in [10, 50, 100].iter() {
        let mut graph: HashMap<i32, Vec<i32>> = HashMap::new();
        
        // 创建网格图
        let n = *size;
        for i in 0..n {
            for j in 0..n {
                let node = i * n + j;
                let mut neighbors = Vec::new();
                if i > 0 { neighbors.push((i - 1) * n + j); }
                if i < n - 1 { neighbors.push((i + 1) * n + j); }
                if j > 0 { neighbors.push(i * n + j - 1); }
                if j < n - 1 { neighbors.push(i * n + j + 1); }
                graph.insert(node, neighbors);
            }
        }

        group.bench_with_input(
            BenchmarkId::new("bfs_grid", size),
            size,
            |b, _| {
                b.iter(|| {
                    graph_bfs_dfs::bfs(black_box(&graph), black_box(0));
                });
            },
        );

        group.bench_with_input(
            BenchmarkId::new("dfs_grid", size),
            size,
            |b, _| {
                b.iter(|| {
                    graph_bfs_dfs::dfs(black_box(&graph), black_box(0));
                });
            },
        );
    }

    // Dijkstra
    for size in [10, 50, 100].iter() {
        let mut edges: Vec<(i32, i32, i32)> = Vec::new();
        let n = *size;
        
        // 创建网格图带权重
        for i in 0..n {
            for j in 0..n {
                let node = i * n + j;
                if i < n - 1 {
                    edges.push((node, node + n, 1));
                }
                if j < n - 1 {
                    edges.push((node, node + 1, 1));
                }
            }
        }

        group.bench_with_input(
            BenchmarkId::new("dijkstra_grid", size),
            size,
            |b, _| {
                b.iter(|| {
                    dijkstra::dijkstra(black_box(&edges), black_box(0));
                });
            },
        );
    }

    group.finish();
}

// ========== 动态规划基准测试 ==========

fn bench_dp(c: &mut Criterion) {
    let mut group = c.benchmark_group("dynamic_programming");

    for size in [100, 500, 1000].iter() {
        // 生成两个序列
        let seq1: Vec<u8> = (0..*size).map(|i| (i % 256) as u8).collect();
        let seq2: Vec<u8> = (0..*size).map(|i| ((i * 3 + 7) % 256) as u8).collect();

        // LCS
        group.bench_with_input(
            BenchmarkId::new("lcs", size),
            size,
            |b, _| {
                b.iter(|| {
                    lcs::lcs(black_box(&seq1), black_box(&seq2));
                });
            },
        );

        // LCS长度（优化版本）
        group.bench_with_input(
            BenchmarkId::new("lcs_length", size),
            size,
            |b, _| {
                b.iter(|| {
                    lcs::lcs_length(black_box(&seq1), black_box(&seq2));
                });
            },
        );
    }

    group.finish();
}

// ========== 贪心算法基准测试 ==========

fn bench_greedy(c: &mut Criterion) {
    let mut group = c.benchmark_group("greedy");

    for size in [100, 1000, 10000].iter() {
        // 生成随机活动
        let activities: Vec<greedy_activity_selection::Activity> = (0..*size)
            .map(|i| {
                let start = i * 2;
                let end = start + 1 + (i % 5);
                greedy_activity_selection::Activity::new(start, end)
            })
            .collect();

        group.bench_with_input(
            BenchmarkId::new("activity_selection", size),
            size,
            |b, _| {
                b.iter(|| {
                    greedy_activity_selection(black_box(&activities));
                });
            },
        );
    }

    group.finish();
}

// ========== 回溯算法基准测试 ==========

fn bench_backtracking(c: &mut Criterion) {
    let mut group = c.benchmark_group("backtracking");

    // N皇后问题 - 小规模
    for n in [4, 6, 8, 10].iter() {
        group.bench_with_input(
            BenchmarkId::new("n_queens_one", n),
            n,
            |b, _| {
                b.iter(|| {
                    backtracking_nqueens::solve_n_queens_one(black_box(*n));
                });
            },
        );
    }

    group.finish();
}

// ========== 组合测试组 ==========

criterion_group!(
    benches,
    bench_sorting,
    bench_searching,
    bench_graph,
    bench_dp,
    bench_greedy,
    bench_backtracking
);

criterion_main!(benches);
