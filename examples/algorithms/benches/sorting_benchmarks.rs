use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use algorithms::sorting::{merge_sort, quick_sort};

fn bench_merge_sort(c: &mut Criterion) {
    let mut group = c.benchmark_group("merge_sort");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let data: Vec<i32> = (0..size).rev().collect();
            b.iter(|| {
                let mut arr = data.clone();
                merge_sort(black_box(&mut arr));
            });
        });
    }
    
    group.finish();
}

fn bench_quick_sort(c: &mut Criterion) {
    let mut group = c.benchmark_group("quick_sort");
    
    for size in [100, 1000, 10000].iter() {
        group.bench_with_input(BenchmarkId::from_parameter(size), size, |b, &size| {
            let data: Vec<i32> = (0..size).rev().collect();
            b.iter(|| {
                let mut arr = data.clone();
                quick_sort(black_box(&mut arr));
            });
        });
    }
    
    group.finish();
}

fn bench_sorting_comparison(c: &mut Criterion) {
    let mut group = c.benchmark_group("sorting_comparison");
    
    let size = 1000;
    let data: Vec<i32> = (0..size).rev().collect();
    
    group.bench_function("merge_sort_1000", |b| {
        b.iter(|| {
            let mut arr = data.clone();
            merge_sort(black_box(&mut arr));
        });
    });
    
    group.bench_function("quick_sort_1000", |b| {
        b.iter(|| {
            let mut arr = data.clone();
            quick_sort(black_box(&mut arr));
        });
    });
    
    group.bench_function("std_sort_1000", |b| {
        b.iter(|| {
            let mut arr = data.clone();
            arr.sort();
        });
    });
    
    group.finish();
}

criterion_group!(benches, bench_merge_sort, bench_quick_sort, bench_sorting_comparison);
criterion_main!(benches);

