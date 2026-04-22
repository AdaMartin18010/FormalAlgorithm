# Java 算法实现

## 概述

Java 实现库位于 `examples/algorithms-java/`，采用 Maven 项目结构，基于 Java 11 与 JUnit 5 测试框架。

## 项目结构

```
algorithms-java/
├── pom.xml
├── TestRunner.java
├── MergeSort.java / QuickSort.java / HeapSort.java
├── BinarySearch.java
├── BFS.java / DFS.java / Dijkstra.java / GraphTraversal.java
├── Knapsack.java / LCS.java / LIS.java / CoinChange.java
├── UnionFind.java
├── StringAlgorithms.java      # KMP、Manacher、Z函数、滚动哈希
├── NumberTheory.java          # GCD、扩展欧几里得、快速幂、Miller-Rabin、筛法
├── TreeAlgorithms.java        # LCA(倍增)、笛卡尔树
├── Geometry.java              # 凸包、最近点对、线段相交
└── AdvancedAlgorithms.java    # 模拟退火
```

## 构建与测试

```bash
cd examples/algorithms-java
mvn compile
mvn test
```

## 类型与面向对象设计

- 算法以**类静态方法**组织，按主题分文件
- 数据结构以**类**封装，使用私有字段与公共 API
- 几何与树算法采用**内部类**封装状态（如 `LCA`、`RollingHash`）

## 与 Rust 主实现的对齐

| Rust | Java | 状态 |
|------|------|------|
| `sorting.rs` | `MergeSort.java` / `QuickSort.java` / `HeapSort.java` | ✅ |
| `binary_search.rs` | `BinarySearch.java` | ✅ |
| `union_find.rs` | `UnionFind.java` | ✅ |
| `kmp.rs` | `StringAlgorithms.kmpSearch()` | ✅ 新增 |
| `dijkstra.rs` | `Dijkstra.java` | ✅ |
| `tree.rs` | `TreeAlgorithms.LCA` | ✅ 新增 |
