# TypeScript 算法实现库

本项目提供核心算法的 TypeScript 教学实现，与 Rust 主实现及 JavaScript 实现对齐，补充严格的静态类型定义。

## 模块索引

| 模块 | 文件 | 核心算法 | 时间复杂度 |
|------|------|---------|-----------|
| 排序 | `sorting.ts` | 快速排序、归并排序、堆排序、计数排序、希尔排序、插入排序、选择排序、冒泡排序、桶排序、基数排序 | O(n log n) ~ O(n²) |
| 数据结构 | `data_structures.ts` | 链表、栈、队列、哈希表、并查集、线段树、树状数组、Trie、跳表 | O(1) ~ O(log n) |
| 搜索 | `search.ts` | 二分搜索、线性搜索、插值搜索、三分搜索 | O(log n) ~ O(n) |
| 图论 | `graph.ts` | BFS、DFS、Dijkstra、Bellman-Ford、Floyd-Warshall、Kruskal、Prim、拓扑排序、强连通分量 | O(V + E) ~ O(V³) |
| 动态规划 | `dynamic_programming.ts` | 0/1 背包、LIS、LCS、零钱问题、编辑距离、矩阵链乘 | O(nW) ~ O(n³) |
| 字符串 | `string.ts` | KMP、Manacher、Z算法、滚动哈希、AC自动机、后缀数组 | O(n) ~ O(n log n) |
| 数论 | `number_theory.ts` | 素性测试、GCD、扩展欧几里得、快速幂、离散对数 | O(log n) ~ O(√n) |
| 计算几何 | `geometry.ts` | 凸包、最近点对、线段相交、方向判断 | O(n log n) |
| 树算法 | `tree.ts` | LCA、树链剖分、重心分解、笛卡尔树 | O(log n) ~ O(n) |
| 高级算法 | `advanced.ts` | FFT、莫队算法、舞蹈链、模拟退火 | O(n log n) ~ O(√n) |

## 快速开始

```bash
cd examples/algorithms-ts
npm install
npm test
```

## 构建

```bash
npm run build
```

## 类型特点

- 严格的泛型类型约束
- 不可变与可变接口分离
- 完整的时间/空间复杂度标注
- 自包含的测试断言（零外部依赖）
