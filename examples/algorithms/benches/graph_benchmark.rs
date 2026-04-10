//! 图算法性能基准测试
//! 
//! 运行方式: cargo bench --bench graph_benchmark

use criterion::{black_box, criterion_group, criterion_main, Criterion, BenchmarkId};
use rand::prelude::*;
use std::collections::{BinaryHeap, HashMap, VecDeque};

// ============== 图结构定义 ==============

/// 图的邻接表表示
#[derive(Clone)]
struct Graph {
    adj: Vec<Vec<(usize, i32)>>, // (邻居, 权重)
    directed: bool,
}

impl Graph {
    fn new(n: usize, directed: bool) -> Self {
        Graph {
            adj: vec![Vec::new(); n],
            directed,
        }
    }
    
    fn add_edge(&mut self, u: usize, v: usize, w: i32) {
        self.adj[u].push((v, w));
        if !self.directed {
            self.adj[v].push((u, w));
        }
    }
    
    fn node_count(&self) -> usize {
        self.adj.len()
    }
}

/// 生成随机图
fn generate_random_graph(n: usize, m: usize, directed: bool) -> Graph {
    let mut graph = Graph::new(n, directed);
    let mut rng = thread_rng();
    let mut edges = 0;
    
    while edges < m {
        let u = rng.gen_range(0..n);
        let v = rng.gen_range(0..n);
        if u != v {
            let w = rng.gen_range(1..100);
            graph.add_edge(u, v, w);
            edges += 1;
        }
    }
    
    graph
}

/// 生成树结构（用于BFS/DFS测试）
fn generate_tree(n: usize) -> Graph {
    let mut graph = Graph::new(n, false);
    let mut rng = thread_rng();
    
    for i in 1..n {
        let parent = rng.gen_range(0..i);
        graph.add_edge(i, parent, 1);
    }
    
    graph
}

/// 生成网格图
fn generate_grid(rows: usize, cols: usize) -> Graph {
    let n = rows * cols;
    let mut graph = Graph::new(n, false);
    
    for r in 0..rows {
        for c in 0..cols {
            let u = r * cols + c;
            
            // 右邻居
            if c + 1 < cols {
                let v = r * cols + (c + 1);
                graph.add_edge(u, v, 1);
            }
            
            // 下邻居
            if r + 1 < rows {
                let v = (r + 1) * cols + c;
                graph.add_edge(u, v, 1);
            }
        }
    }
    
    graph
}

// ============== 图算法实现 ==============

/// BFS - 广度优先搜索
fn bfs(graph: &Graph, start: usize) -> Vec<i32> {
    let n = graph.node_count();
    let mut dist = vec![-1; n];
    let mut queue = VecDeque::new();
    
    dist[start] = 0;
    queue.push_back(start);
    
    while let Some(u) = queue.pop_front() {
        for &(v, _) in &graph.adj[u] {
            if dist[v] == -1 {
                dist[v] = dist[u] + 1;
                queue.push_back(v);
            }
        }
    }
    
    dist
}

/// DFS - 深度优先搜索（递归）
fn dfs_recursive(graph: &Graph, start: usize) -> Vec<bool> {
    let n = graph.node_count();
    let mut visited = vec![false; n];
    
    fn dfs_util(graph: &Graph, u: usize, visited: &mut [bool]) {
        visited[u] = true;
        for &(v, _) in &graph.adj[u] {
            if !visited[v] {
                dfs_util(graph, v, visited);
            }
        }
    }
    
    dfs_util(graph, start, &mut visited);
    visited
}

/// DFS - 深度优先搜索（迭代）
fn dfs_iterative(graph: &Graph, start: usize) -> Vec<bool> {
    let n = graph.node_count();
    let mut visited = vec![false; n];
    let mut stack = vec![start];
    
    while let Some(u) = stack.pop() {
        if visited[u] {
            continue;
        }
        visited[u] = true;
        
        for &(v, _) in &graph.adj[u] {
            if !visited[v] {
                stack.push(v);
            }
        }
    }
    
    visited
}

/// Dijkstra 算法 - 单源最短路径
fn dijkstra(graph: &Graph, start: usize) -> Vec<i32> {
    let n = graph.node_count();
    let INF = i32::MAX;
    let mut dist = vec![INF; n];
    let mut visited = vec![false; n];
    
    dist[start] = 0;
    
    for _ in 0..n {
        // 找到未访问的最小距离节点
        let mut u = n;
        let mut min_dist = INF;
        for i in 0..n {
            if !visited[i] && dist[i] < min_dist {
                min_dist = dist[i];
                u = i;
            }
        }
        
        if u == n {
            break;
        }
        
        visited[u] = true;
        
        // 更新邻居
        for &(v, w) in &graph.adj[u] {
            if !visited[v] && dist[u] + w < dist[v] {
                dist[v] = dist[u] + w;
            }
        }
    }
    
    dist
}

/// Dijkstra 算法 - 优先队列优化
fn dijkstra_heap(graph: &Graph, start: usize) -> Vec<i32> {
    let n = graph.node_count();
    let INF = i32::MAX;
    let mut dist = vec![INF; n];
    
    dist[start] = 0;
    let mut pq = BinaryHeap::new();
    pq.push(std::cmp::Reverse((0, start)));
    
    while let Some(std::cmp::Reverse((d, u))) = pq.pop() {
        if d > dist[u] {
            continue;
        }
        
        for &(v, w) in &graph.adj[u] {
            let new_dist = dist[u] + w;
            if new_dist < dist[v] {
                dist[v] = new_dist;
                pq.push(std::cmp::Reverse((new_dist, v)));
            }
        }
    }
    
    dist
}

/// Floyd-Warshall 算法 - 全源最短路径
fn floyd_warshall(graph: &Graph) -> Vec<Vec<i32>> {
    let n = graph.node_count();
    let INF = i32::MAX / 2; // 防止溢出
    
    // 初始化距离矩阵
    let mut dist = vec![vec![INF; n]; n];
    for i in 0..n {
        dist[i][i] = 0;
    }
    
    for u in 0..n {
        for &(v, w) in &graph.adj[u] {
            dist[u][v] = w.min(dist[u][v]);
        }
    }
    
    // Floyd-Warshall
    for k in 0..n {
        for i in 0..n {
            for j in 0..n {
                if dist[i][k] + dist[k][j] < dist[i][j] {
                    dist[i][j] = dist[i][k] + dist[k][j];
                }
            }
        }
    }
    
    dist
}

/// 拓扑排序 - Kahn算法
fn topological_sort(graph: &Graph) -> Option<Vec<usize>> {
    let n = graph.node_count();
    let mut in_degree = vec![0; n];
    
    // 计算入度
    for u in 0..n {
        for &(v, _) in &graph.adj[u] {
            in_degree[v] += 1;
        }
    }
    
    let mut queue = VecDeque::new();
    let mut result = Vec::new();
    
    // 入度为0的节点入队
    for i in 0..n {
        if in_degree[i] == 0 {
            queue.push_back(i);
        }
    }
    
    while let Some(u) = queue.pop_front() {
        result.push(u);
        
        for &(v, _) in &graph.adj[u] {
            in_degree[v] -= 1;
            if in_degree[v] == 0 {
                queue.push_back(v);
            }
        }
    }
    
    if result.len() == n {
        Some(result)
    } else {
        None // 有环
    }
}

/// 并查集
struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }
    
    fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    fn union(&mut self, x: usize, y: usize) -> bool {
        let px = self.find(x);
        let py = self.find(y);
        
        if px == py {
            return false;
        }
        
        if self.rank[px] < self.rank[py] {
            self.parent[px] = py;
        } else if self.rank[px] > self.rank[py] {
            self.parent[py] = px;
        } else {
            self.parent[py] = px;
            self.rank[px] += 1;
        }
        
        true
    }
}

/// Kruskal 算法 - 最小生成树
fn kruskal(n: usize, edges: &[(usize, usize, i32)]) -> i32 {
    let mut uf = UnionFind::new(n);
    let mut edges: Vec<_> = edges.to_vec();
    edges.sort_by_key(|e| e.2);
    
    let mut mst_weight = 0;
    let mut edges_used = 0;
    
    for (u, v, w) in edges {
        if uf.union(u, v) {
            mst_weight += w;
            edges_used += 1;
            if edges_used == n - 1 {
                break;
            }
        }
    }
    
    mst_weight
}

// ============== 基准测试 ==============

fn bench_traversal(c: &mut Criterion) {
    let mut group = c.benchmark_group("Graph Traversal");
    
    for size in [100, 1_000, 10_000].iter() {
        let tree = generate_tree(*size);
        
        group.bench_with_input(
            BenchmarkId::new("BFS", size),
            size,
            |b, _| {
                b.iter(|| {
                    black_box(bfs(&tree, 0));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("DFS Recursive", size),
            size,
            |b, _| {
                b.iter(|| {
                    black_box(dfs_recursive(&tree, 0));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("DFS Iterative", size),
            size,
            |b, _| {
                b.iter(|| {
                    black_box(dfs_iterative(&tree, 0));
                });
            },
        );
    }
    
    group.finish();
}

fn bench_shortest_path(c: &mut Criterion) {
    let mut group = c.benchmark_group("Shortest Path");
    
    for size in [50, 100, 200].iter() {
        // 生成稠密图用于Floyd测试
        let n = *size;
        let m = n * 5; // 平均每个节点5条边
        let graph = generate_random_graph(n, m, false);
        
        group.bench_with_input(
            BenchmarkId::new("Dijkstra (Array)", size),
            size,
            |b, _| {
                b.iter(|| {
                    black_box(dijkstra(&graph, 0));
                });
            },
        );
        
        group.bench_with_input(
            BenchmarkId::new("Dijkstra (Heap)", size),
            size,
            |b, _| {
                b.iter(|| {
                    black_box(dijkstra_heap(&graph, 0));
                });
            },
        );
        
        // Floyd只测试小图
        if *size <= 100 {
            group.bench_with_input(
                BenchmarkId::new("Floyd-Warshall", size),
                size,
                |b, _| {
                    b.iter(|| {
                        black_box(floyd_warshall(&graph));
                    });
                },
            );
        }
    }
    
    group.finish();
}

fn bench_mst(c: &mut Criterion) {
    let mut group = c.benchmark_group("Minimum Spanning Tree");
    
    for size in [100, 500, 1_000].iter() {
        let n = *size;
        let m = n * 3;
        let graph = generate_random_graph(n, m, false);
        
        // 提取边
        let mut edges = Vec::new();
        for u in 0..n {
            for &(v, w) in &graph.adj[u] {
                if u < v { // 避免重复边
                    edges.push((u, v, w));
                }
            }
        }
        
        group.bench_with_input(
            BenchmarkId::new("Kruskal", size),
            size,
            move |b, _| {
                b.iter(|| {
                    black_box(kruskal(n, &edges));
                });
            },
        );
    }
    
    group.finish();
}

fn bench_grid_graph(c: &mut Criterion) {
    let mut group = c.benchmark_group("Grid Graph BFS");
    
    for dim in [10, 50, 100].iter() {
        let grid = generate_grid(*dim, *dim);
        
        group.bench_with_input(
            BenchmarkId::new("BFS", dim),
            dim,
            |b, _| {
                b.iter(|| {
                    black_box(bfs(&grid, 0));
                });
            },
        );
    }
    
    group.finish();
}

criterion_group!(
    benches,
    bench_traversal,
    bench_shortest_path,
    bench_mst,
    bench_grid_graph
);
criterion_main!(benches);

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_bfs_dfs() {
        let mut graph = Graph::new(5, false);
        graph.add_edge(0, 1, 1);
        graph.add_edge(0, 2, 1);
        graph.add_edge(1, 3, 1);
        graph.add_edge(2, 4, 1);
        
        let bfs_result = bfs(&graph, 0);
        assert_eq!(bfs_result, vec![0, 1, 1, 2, 2]);
        
        let dfs_result = dfs_recursive(&graph, 0);
        assert!(dfs_result[0]);
        assert!(dfs_result[1]);
        assert!(dfs_result[4]);
    }
    
    #[test]
    fn test_dijkstra() {
        let mut graph = Graph::new(4, false);
        graph.add_edge(0, 1, 4);
        graph.add_edge(0, 2, 1);
        graph.add_edge(2, 1, 2);
        graph.add_edge(1, 3, 1);
        graph.add_edge(2, 3, 5);
        
        let dist = dijkstra(&graph, 0);
        assert_eq!(dist, vec![0, 3, 1, 4]);
    }
    
    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);
        assert!(uf.union(0, 1));
        assert!(uf.union(1, 2));
        assert!(!uf.union(0, 2)); // 已在同一集合
        assert_eq!(uf.find(0), uf.find(2));
        assert_ne!(uf.find(0), uf.find(3));
    }
}
