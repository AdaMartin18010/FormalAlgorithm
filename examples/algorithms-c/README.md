# C 算法实现库

本项目提供核心算法的 C 语言教学实现，与 Rust 主实现对齐。

## 模块索引

| 模块 | 文件 | 核心算法 | 时间复杂度 |
|------|------|---------|-----------|
| 排序 | `sorting.c` | 快速排序、归并排序、堆排序、计数排序 | O(n log n) ~ O(n + k) |
| 数据结构 | `data_structures.c` | 链表、栈、队列 | O(1) ~ O(n) |
| 搜索 | `search.c` | 二分搜索、下界、上界 | O(log n) |
| 图论 | `graph.c` | BFS、DFS | O(V + E) |
| 动态规划 | `dynamic.c` | 0/1 背包、LIS、零钱问题 | O(nW) ~ O(n log n) |
| 并查集 | `union_find.c` | Union-Find（路径压缩 + 按秩合并） | O(α(n)) |

## 快速开始

```bash
cd examples/algorithms-c
gcc -std=c99 -Wall search.c -o search_test && ./search_test
gcc -std=c99 -Wall graph.c -o graph_test && ./graph_test
gcc -std=c99 -Wall dynamic.c -o dynamic_test && ./dynamic_test
gcc -std=c99 -Wall union_find.c -o uf_test && ./uf_test
```

## 编译说明

所有模块使用 C99 标准，仅依赖标准库。每个源文件包含独立的 `main()` 函数用于验证。
