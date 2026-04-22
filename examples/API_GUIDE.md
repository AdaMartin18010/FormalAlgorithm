# FormalAlgorithm 多语言 API 对齐规范

本规范定义七语言算法实现库的统一接口设计原则，确保跨语言的一致性与可维护性。

## 语言矩阵

| 语言 | 目录 | 测试框架 | 构建工具 |
|------|------|---------|---------|
| Rust | `examples/algorithms/` | 内置 `cargo test` | Cargo |
| Python | `examples/algorithms-python/` | pytest | pip |
| Go | `examples/algorithms-go/` | `go test` | Go Modules |
| Java | `examples/algorithms-java/` | JUnit 5 | Maven |
| C++ | `examples/algorithms-cpp/` | 内置 `main()` assert | CMake |
| JavaScript | `examples/algorithms-js/` | 内置 `runTests()` | Node.js |
| C | `examples/algorithms-c/` | 内置 `main()` assert | gcc/clang |

## 核心算法覆盖

所有语言至少覆盖以下 5 个核心领域：

| 领域 | 必选算法 |
|------|---------|
| 排序 | 快速排序、归并排序、堆排序 |
| 搜索 | 二分搜索（含 lower/upper bound） |
| 图论 | BFS、DFS、最短路径（Dijkstra） |
| 动态规划 | 0/1 背包、最长递增子序列 |
| 数据结构 | 并查集（Union-Find） |

## 命名规范

| 语言 | 模块命名 | 函数命名 | 常量命名 |
|------|---------|---------|---------|
| Rust | `snake_case` | `snake_case` | `SCREAMING_SNAKE_CASE` |
| Python | `snake_case` | `snake_case` | `SCREAMING_SNAKE_CASE` |
| Go | `snake_case` | `CamelCase` (exported) | `CamelCase` |
| Java | `PascalCase` | `camelCase` | `SCREAMING_SNAKE_CASE` |
| C++ | `snake_case` | `snake_case` | `SCREAMING_SNAKE_CASE` |
| JS | `camelCase` | `camelCase` | `SCREAMING_SNAKE_CASE` |
| C | `snake_case` | `snake_case` | `SCREAMING_SNAKE_CASE` |

## 注释规范

所有公共接口必须包含：

1. **功能描述**：一句话说明算法功能
2. **复杂度标注**：时间复杂度和空间复杂度
3. **参数说明**：输入参数类型和约束

## 测试规范

- **边界条件**：空输入、单元素、最大值
- **正确性验证**：与已知正确结果对比
- **稳定性**：对已有序数据的表现

## 复杂度标注格式

统一使用大 O 表示法：

```
时间复杂度: O(n log n)
空间复杂度: O(n)
```
