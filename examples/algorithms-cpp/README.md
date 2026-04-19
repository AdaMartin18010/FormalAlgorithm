# C++ 算法实现库

本项目提供核心算法的 C++17 教学实现，与 Rust 主实现对齐。

## 模块索引

| 模块 | 文件 | 核心算法 | 时间复杂度 |
|------|------|---------|-----------|
| 排序 | `sorting.cpp` | 快速排序、归并排序、堆排序、计数排序、希尔排序 | O(n log n) ~ O(n + k) |
| 图论 | `graph.cpp` | Dijkstra、BFS、DFS、Floyd-Warshall、拓扑排序 | O(V + E) ~ O(V³) |
| 线段树 | `segment_tree.cpp` | 区间查询、区间更新、延迟传播 | O(log n) |
| 搜索 | `search.cpp` | 二分搜索、下界、上界 | O(log n) |
| 动态规划 | `dynamic.cpp` | 0/1 背包、LIS、零钱问题 | O(nW) ~ O(n log n) |
| 并查集 | `union_find.cpp` | Union-Find（路径压缩 + 按秩合并） | O(α(n)) |

## 快速开始

```bash
cd examples/algorithms-cpp
mkdir build && cd build
cmake ..
cmake --build .
ctest
```

## 编译说明

使用 CMake 构建系统，要求 C++17。每个模块为独立可执行文件，包含内置测试。
