# Go 算法实现库

本项目提供核心算法的 Go 语言教学实现，与 Rust 主实现对齐。

## 模块索引

| 模块 | 文件 | 核心算法 | 时间复杂度 |
|------|------|---------|-----------|
| 排序 | `sorting.go` | QuickSort, MergeSort, HeapSort, InsertionSort, CountingSort | O(n log n) ~ O(n + k) |
| 搜索 | `search.go` | BinarySearch, LowerBound, UpperBound | O(log n) |
| 图论 | `graph.go` | BFS, DFS, Dijkstra | O(V + E) ~ O((V+E) log V) |
| 动态规划 | `dynamic.go` | 0/1 背包, LIS, 零钱问题 | O(nW) ~ O(n log n) |
| 并查集 | `unionfind.go` | Union-Find (路径压缩 + 按秩合并) | O(α(n)) |

## 快速开始

```bash
cd examples/algorithms-go
go test -v ./...
```

## 测试覆盖

运行 `go test -v ./...` 执行全部单元测试。
