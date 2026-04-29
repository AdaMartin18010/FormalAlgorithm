use criterion::{black_box, criterion_group, criterion_main, Criterion};
use algorithms::genetic_algorithm::{GeneticAlgorithm, SelectionMethod};
use algorithms::ant_colony::{aco_tsp, TspGraph};
use algorithms::tabu_search::tabu_sort;

fn bench_genetic_algorithm(c: &mut Criterion) {
    let ga = GeneticAlgorithm::new(50, 0.8, 0.01, SelectionMethod::Tournament(3));
    c.bench_function("ga_onemax_20", |b| {
        b.iter(|| {
            ga.optimize(
                |chrom| chrom.iter().filter(|&&b| b).count() as f64,
                black_box(100),
                black_box(20),
            )
        })
    });
}

fn bench_ant_colony(c: &mut Criterion) {
    let graph = TspGraph::new(vec![
        vec![0.0, 2.0, 9.0, 10.0],
        vec![2.0, 0.0, 6.0, 4.0],
        vec![9.0, 6.0, 0.0, 8.0],
        vec![10.0, 4.0, 8.0, 0.0],
    ]);
    c.bench_function("aco_tsp_4nodes", |b| {
        b.iter(|| aco_tsp(black_box(&graph), black_box(20), black_box(50), black_box(1.0), black_box(2.0), black_box(0.5)))
    });
}

fn bench_tabu_search(c: &mut Criterion) {
    c.bench_function("tabu_sort_50", |b| {
        let mut arr: Vec<i32> = (1..=50).rev().collect();
        b.iter(|| {
            let mut a = arr.clone();
            tabu_sort(black_box(&mut a));
            a
        })
    });
}

criterion_group!(
    benches,
    bench_genetic_algorithm,
    bench_ant_colony,
    bench_tabu_search
);
criterion_main!(benches);
