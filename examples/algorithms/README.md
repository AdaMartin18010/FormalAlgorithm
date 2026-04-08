# 工程级算法实现库 (Engineering-Level Algorithm Library)

本项目提供10个核心算法的工程级实现，包含完整的文档、单元测试和性能基准测试。

## 📦 安装

```toml
[dependencies]
formal-algorithms = "0.1.0"
```

## 🚀 快速开始

```rust
use formal_algorithms::{merge_sort, quick_sort, binary_search, dijkstra};

fn main() {
    // 排序
    let mut data = vec![64, 34, 25, 12, 22, 11, 90];
    merge_sort(&mut data);
    println!("归并排序结果: {:?}", data);

    // 搜索
    let arr = vec![1, 3, 5, 7, 9, 11, 13];
    match binary_search(&arr, 7) {
        Ok(idx) => println!("找到元素 7 在索引 {}", idx),
        Err(_) => println!("元素未找到"),
    }

    // 图算法
    let edges = vec![
        ('A', 'B', 4),
        ('A', 'C', 2),
        ('B', 'C', 1),
        ('B', 'D', 5),
        ('C', 'D', 8),
    ];
    let (distances, predecessors) = dijkstra(&edges, 'A');
    println!("从 A 出发的最短距离: {:?}", distances);
}
```

## 📚 算法清单

| 分类 | 算法 | 模块 | 时间复杂度 | 空间复杂度 | 特点 |
|------|------|------|-----------|-----------|------|
| 排序 | 归并排序 | `merge_sort` | O(n log n) | O(n) | 稳定排序，分治法 |
| 排序 | 快速排序 | `quick_sort` | O(n log n) 平均 | O(log n) | 原地排序，分治法 |
| 排序 | 堆排序 | `heap_sort` | O(n log n) | O(1) | 原地排序，堆结构 |
| 搜索 | 二分搜索 | `binary_search` | O(log n) | O(1) | 有序数组搜索 |
| 图算法 | Dijkstra | `dijkstra` | O((V+E) log V) | O(V) | 单源最短路径 |
| 图算法 | BFS | `graph_bfs_dfs::bfs` | O(V+E) | O(V) | 广度优先搜索 |
| 图算法 | DFS | `graph_bfs_dfs::dfs` | O(V+E) | O(V) | 深度优先搜索 |
| 动态规划 | LCS | `lcs` | O(mn) | O(mn) 可优化 | 最长公共子序列 |
| 贪心算法 | 活动选择 | `greedy_activity_selection` | O(n log n) | O(n) | 区间调度问题 |
| 回溯算法 | N皇后 | `backtracking_nqueens` | O(N!) | O(N) | 经典回溯问题 |

## 🔧 功能特性

### 类型安全

- 使用Rust类型系统确保运行时安全
- 泛型支持多种数据类型
- 自定义错误类型

### 错误处理

- 使用 `Result<T, E>` 进行错误传播
- 使用 `Option<T>` 处理可选值
- 详细的错误信息和上下文

### 性能优化

- 零成本抽象
- 内存安全无GC开销
- 编译器优化友好

## 🧪 测试

### 运行所有测试

```bash
cargo test
```

### 运行特定算法测试

```bash
cargo test merge_sort
cargo test quick_sort
cargo test binary_search
```

### 边界条件测试

```bash
cargo test -- --include-ignored
```

## 📊 基准测试

### 运行所有基准测试

```bash
cargo bench
```

### 生成HTML报告

基准测试报告将生成在 `target/criterion/` 目录下。

### 与标准库对比

```bash
cargo bench -- --compare
```

## 📖 算法详解

### 1. 归并排序 (Merge Sort)

```rust
use formal_algorithms::merge_sort;

let mut data = vec![38, 27, 43, 3, 9, 82, 10];
merge_sort(&mut data);
assert_eq!(data, vec![3, 9, 10, 27, 38, 43, 82]);
```

**算法思想**: 分治法 - 将数组分成两半，分别排序后合并。

**复杂度分析**:

- 时间复杂度: O(n log n) - 最坏、最好、平均情况
- 空间复杂度: O(n) - 需要额外存储空间
- 稳定性: 稳定

### 2. 快速排序 (Quick Sort)

```rust
use formal_algorithms::quick_sort;

let mut data = vec![10, 7, 8, 9, 1, 5];
quick_sort(&mut data);
assert_eq!(data, vec![1, 5, 7, 8, 9, 10]);
```

**算法思想**: 分治法 - 选择基准元素，将数组分区后递归排序。

**复杂度分析**:

- 时间复杂度: O(n log n) 平均，O(n²) 最坏
- 空间复杂度: O(log n) - 递归栈空间
- 稳定性: 不稳定

### 3. 堆排序 (Heap Sort)

```rust
use formal_algorithms::heap_sort;

let mut data = vec![12, 11, 13, 5, 6, 7];
heap_sort(&mut data);
assert_eq!(data, vec![5, 6, 7, 11, 12, 13]);
```

**算法思想**: 构建最大堆，反复提取最大值。

**复杂度分析**:

- 时间复杂度: O(n log n)
- 空间复杂度: O(1) - 原地排序
- 稳定性: 不稳定

### 4. 二分搜索 (Binary Search)

```rust
use formal_algorithms::binary_search;

let arr = vec![2, 3, 4, 10, 40];
assert_eq!(binary_search(&arr, 10), Ok(3));
assert_eq!(binary_search(&arr, 5), Err(SearchError::NotFound));
```

**算法思想**: 在有序数组中，每次将搜索范围减半。

**复杂度分析**:

- 时间复杂度: O(log n)
- 空间复杂度: O(1)

### 5. Dijkstra算法

```rust
use formal_algorithms::dijkstra;

let edges = vec![
    ('A', 'B', 4),
    ('A', 'C', 2),
    ('B', 'C', 1),
    ('B', 'D', 5),
];
let (distances, predecessors) = dijkstra(&edges, 'A');
```

**算法思想**: 贪心算法 - 每次选择距离最短的顶点进行松弛操作。

**复杂度分析**:

- 时间复杂度: O((V+E) log V) 使用优先队列
- 空间复杂度: O(V)

### 6. 最长公共子序列 (LCS)

```rust
use formal_algorithms::lcs;

let seq1 = vec![1, 3, 4, 1, 2, 1, 3];
let seq2 = vec![3, 4, 1, 2, 1, 3, 2];
let (length, subsequence) = lcs(&seq1, &seq2);
```

**算法思想**: 动态规划 - 构建DP表存储子问题解。

**复杂度分析**:

- 时间复杂度: O(mn)
- 空间复杂度: O(mn) 可优化至 O(min(m,n))

### 7. 活动选择问题

```rust
use formal_algorithms::greedy_activity_selection;

let activities = vec![
    Activity { start: 1, finish: 4 },
    Activity { start: 3, finish: 5 },
    Activity { start: 0, finish: 6 },
];
let selected = greedy_activity_selection(&activities);
```

**算法思想**: 贪心算法 - 每次选择结束时间最早且兼容的活动。

**复杂度分析**:

- 时间复杂度: O(n log n) - 主要是排序
- 空间复杂度: O(n)

### 9. N皇后问题

```rust
use formal_algorithms::solve_n_queens;

let solutions = solve_n_queens(4);
println!("4皇后问题共有 {} 个解", solutions.len());
```

**算法思想**: 回溯算法 - 逐行放置皇后，冲突时回溯。

**复杂度分析**:

- 时间复杂度: O(N!) 最坏情况
- 空间复杂度: O(N) - 递归栈

### 10. 活动选择问题

```rust
use formal_algorithms::greedy_activity_selection::{greedy_activity_selection, Activity};

let activities = vec![
    Activity::new(1, 4),
    Activity::new(3, 5),
    Activity::new(0, 6),
    Activity::new(5, 7),
];
let result = greedy_activity_selection(&activities);
println!("最多可以安排 {} 个活动", result.count);
```

**算法思想**: 贪心算法 - 每次选择结束时间最早且兼容的活动。

**复杂度分析**:

- 时间复杂度: O(n log n) - 主要是排序
- 空间复杂度: O(n)

### 11. 图的BFS/DFS遍历

```rust
use formal_algorithms::{bfs, dfs};

let adjacency_list = vec![
    vec![1, 2],    // 顶点0的邻接点
    vec![0, 3, 4], // 顶点1的邻接点
    vec![0, 5],    // 顶点2的邻接点
];

let bfs_order = bfs(&adjacency_list, 0);
let dfs_order = dfs(&adjacency_list, 0);
```

**算法思想**:

- BFS: 队列实现的层次遍历
- DFS: 栈/递归实现的深度遍历

**复杂度分析**:

- 时间复杂度: O(V+E)
- 空间复杂度: O(V)

## 📄 许可证

本项目采用 MIT OR Apache-2.0 双许可证。

## 🤝 贡献

欢迎提交Issue和Pull Request。请确保：

1. 代码符合Rust编码规范
2. 包含完整的单元测试
3. 更新相关文档
