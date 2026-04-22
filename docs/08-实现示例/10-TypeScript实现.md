# TypeScript 算法实现

## 概述

TypeScript 实现库位于 `examples/algorithms-ts/`，是项目代码示例体系的重要组成部分。该实现以**严格的静态类型系统**为核心特色，为算法教学提供了类型安全的参考实现，与 Rust 主实现、JavaScript 实现对齐。

## 项目结构

```
algorithms-ts/
├── package.json          # npm 配置
├── tsconfig.json         # TypeScript 严格模式配置
├── README.md
└── src/
    ├── index.ts          # 统一入口
    ├── utils.ts          # 泛型工具与零依赖测试框架
    ├── sorting.ts        # 10 种排序算法
    ├── data_structures.ts # 8 种数据结构
    ├── search.ts         # 4 种搜索算法
    ├── graph.ts          # 9 种图论算法
    ├── dynamic_programming.ts # 7 种 DP 算法
    ├── string.ts         # 6 种字符串算法
    ├── number_theory.ts  # 8 种数论算法
    ├── geometry.ts       # 3 种计算几何算法
    ├── tree.ts           # 4 种树算法
    ├── advanced.ts       # 4 种高级算法
    └── tests/
        └── all_tests.ts  # 统一测试运行器
```

## 类型设计特点

### 1. 泛型约束

所有排序与搜索算法均支持泛型类型参数与自定义比较函数：

```typescript
export type CompareFn<T> = (a: T, b: T) => number;

export function quickSort<T>(arr: T[], compare: CompareFn<T> = defaultCompare): T[] {
  // 实现与具体类型解耦
}
```

### 2. 严格的不可变性标注

数据结构通过私有字段与只读 getter 控制外部可变性：

```typescript
export class Stack<T> {
  private items: T[] = [];
  get size(): number { return this.items.length; }
  push(item: T): void { this.items.push(item); }
  // ...
}
```

### 3. 完整的时间/空间复杂度标注

每个算法均附带 JSDoc 注释，明确标注：

- 时间复杂度（最坏/平均/最好）
- 空间复杂度
- 稳定性（排序算法）

## 算法覆盖清单

| 类别 | 算法 | 文件 |
|------|------|------|
| 排序 | 冒泡、选择、插入、希尔、归并、快速、堆、计数、桶、基数 | `sorting.ts` |
| 数据结构 | 链表、栈、队列、并查集、线段树、树状数组、Trie、跳表 | `data_structures.ts` |
| 搜索 | 线性、二分、插值、三分 | `search.ts` |
| 图论 | BFS、DFS、Dijkstra、Bellman-Ford、Floyd-Warshall、Kruskal、Prim、拓扑排序、Kosaraju | `graph.ts` |
| 动态规划 | 0/1背包、完全背包、LIS、LCS、零钱、编辑距离、矩阵链乘 | `dynamic_programming.ts` |
| 字符串 | KMP、Manacher、Z函数、滚动哈希、AC自动机、后缀数组+LCP | `string.ts` |
| 数论 | GCD/LCM、扩展欧几里得、模逆元、快速幂、Miller-Rabin、筛法、离散对数 | `number_theory.ts` |
| 计算几何 | 凸包、最近点对、线段相交 | `geometry.ts` |
| 树 | LCA(倍增)、树链剖分、重心分解、笛卡尔树 | `tree.ts` |
| 高级 | FFT、莫队、舞蹈链、模拟退火 | `advanced.ts` |

## 测试体系

采用**零外部依赖**的自包含测试框架：

```typescript
import { runTests, assertEq, assertArrayEq, assertTrue } from "./utils";

export function runSortingTests(): void {
  runTests("Sorting", {
    "quickSort basic": () => {
      assertArrayEq(quickSort([10, 7, 8, 9, 1, 5]), [1, 5, 7, 8, 9, 10]);
    },
    // ...
  });
}
```

### 测试结果

```
Total: 10 modules, 72 tests, 0 failed
```

## 构建与运行

```bash
cd examples/algorithms-ts
npm install
npm run build   # tsc 编译
npm test        # 运行全部测试
```

## 与 Rust 主实现的对齐

| Rust 实现 | TypeScript 实现 | 对齐状态 |
|-----------|----------------|----------|
| `sorting.rs` | `sorting.ts` | ✅ 10 种排序全覆盖 |
| `union_find.rs` | `UnionFind` 类 | ✅ 路径压缩 + 按秩合并 |
| `segment_tree.rs` | `SegmentTree` 类 | ✅ 区间求和 + 单点更新 |
| `fenwick_tree.rs` | `FenwickTree` 类 | ✅ 树状数组标准实现 |
| `dijkstra.rs` | `dijkstra()` | ✅ 稠密图 O(V²) 版本 |
| `kmp.rs` | `kmpSearch()` | ✅ 前缀函数 + 搜索 |
| `fft.rs` | `multiplyPolynomials()` | ✅ 复数 FFT 实现 |
| `mo_algorithm.rs` | `moAlgorithm()` | ✅ 离线区间查询框架 |
| `dancing_links.rs` | `DancingLinks` 类 | ✅ Exact Cover / DLX |

## 类型理论视角

TypeScript 的**结构化类型系统**与本项目的类型理论模块（`docs/05-类型理论/`）形成呼应：

- **泛型参数**对应简单类型论中的类型变量
- **条件类型**（虽未在本实现中使用）对应依赖类型的轻量形式
- **接口与类**的区分体现了类型与实现的分离

## 后续扩展方向

1. **添加性能基准测试**：与 Rust 实现进行横向对比
2. **引入类型级编程**：利用 TypeScript 的类型系统实现编译期计算示例
3. **生成声明文件**：`dist/*.d.ts` 已自动生成，可作为类型规范文档
4. **并行算法**：利用 Web Workers 实现多线程排序/搜索示例
