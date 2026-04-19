# JavaScript 算法实现库

本项目提供核心算法的 JavaScript/Node.js 教学实现，与 Rust 主实现对齐。

## 模块索引

| 模块 | 文件 | 核心算法 | 时间复杂度 |
|------|------|---------|-----------|
| 排序 | `sorting.js` | 快速排序、归并排序、堆排序、计数排序、希尔排序 | O(n log n) ~ O(n + k) |
| 数据结构 | `data_structures.js` | 链表、栈、队列、哈希表 | O(1) ~ O(n) |
| 搜索 | `search.js` | 二分搜索、下界、上界 | O(log n) |
| 图论 | `graph.js` | BFS、DFS、路径判断 | O(V + E) |
| 动态规划 | `dynamic.js` | 0/1 背包、LIS、零钱问题 | O(nW) ~ O(n log n) |

## 快速开始

```bash
cd examples/algorithms-js
npm test
```

## 测试说明

每个模块包含独立的 `runTests()` 函数，使用 `assertEq` 进行验证。运行对应文件即可执行测试。
