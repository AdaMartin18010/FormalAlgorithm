# 算法实现示例 / Algorithm Implementation Examples

> **说明**: 本目录包含经典算法的Rust实现，配有单元测试和性能基准测试。这些实现旨在展示算法的形式化定义如何转化为可运行的代码。

**This directory contains Rust implementations of classic algorithms, with unit tests and performance benchmarks. These implementations demonstrate how formal algorithm definitions translate into executable code.**

---

## 📋 实现清单 / Implementation List

### 排序算法 / Sorting Algorithms

1. **归并排序** (`merge_sort.rs`)
   - 时间复杂度: O(n log n)
   - 空间复杂度: O(n)
   - 稳定性: 稳定
   - 特点: 分治策略的经典应用

2. **快速排序** (`quick_sort.rs`)
   - 平均时间复杂度: O(n log n)
   - 最坏时间复杂度: O(n²)
   - 空间复杂度: O(log n)
   - 特点: 原地排序，实践中性能优异

### 搜索算法 / Search Algorithms

1. **二分搜索** (`binary_search.rs`)
   - 时间复杂度: O(log n)
   - 空间复杂度: O(1)
   - 前提条件: 数组已排序
   - 特点: 对数时间复杂度的经典算法

### 动态规划 / Dynamic Programming

1. **最长公共子序列 (LCS)** (`longest_common_subsequence.rs`)
   - 时间复杂度: O(m × n)
   - 空间复杂度: O(m × n)
   - 应用: 文本比较、生物信息学
   - 特点: 动态规划的经典问题

### 图算法 / Graph Algorithms

1. **Dijkstra最短路径** (`dijkstra.rs`)
   - 时间复杂度: O((V + E) log V) (使用优先队列)
   - 空间复杂度: O(V)
   - 应用: 路径规划、网络路由
   - 特点: 贪心策略，适用于非负权重图

---

## 🚀 使用方法 / Usage

### 编译和测试

```bash
# 编译所有算法
cargo build --release

# 运行所有测试
cargo test

# 运行特定算法的测试
cargo test merge_sort

# 运行基准测试
cargo bench
```

### 代码示例

```rust
use algorithms::sorting::merge_sort;

fn main() {
    let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
    merge_sort(&mut arr);
    println!("排序后: {:?}", arr);
}
```

---

## 📊 性能基准 / Performance Benchmarks

基准测试使用 `criterion` 库，测试不同规模输入下的性能：

- 小规模: 100 个元素
- 中规模: 10,000 个元素
- 大规模: 1,000,000 个元素

运行基准测试：

```bash
cargo bench --bench sorting_benchmarks
```

---

## 🧪 测试覆盖 / Test Coverage

每个算法实现包含：

1. **单元测试**
   - 基本功能测试
   - 边界条件测试（空数组、单元素、已排序等）
   - 正确性验证

2. **属性测试** (使用 `proptest`)
   - 随机输入测试
   - 不变量验证

3. **性能测试**
   - 时间复杂度验证
   - 不同输入规模的性能对比

---

## 📚 形式化规范 / Formal Specifications

每个算法实现都对应项目文档中的形式化定义：

| 算法 | 形式化文档 | 实现文件 |
|------|-----------|---------|
| 归并排序 | `09-算法理论/02-算法设计范式/01-分治策略.md` | `merge_sort.rs` |
| 快速排序 | `09-算法理论/02-算法设计范式/01-分治策略.md` | `quick_sort.rs` |
| 二分搜索 | `09-算法理论/01-算法基础/02-算法分析.md` | `binary_search.rs` |
| LCS | `09-算法理论/02-算法设计范式/02-动态规划.md` | `longest_common_subsequence.rs` |
| Dijkstra | `09-算法理论/03-图论算法/01-最短路径.md` | `dijkstra.rs` |

---

## 🔧 依赖 / Dependencies

```toml
[dependencies]
# 无运行时依赖

[dev-dependencies]
criterion = "0.5"      # 性能基准测试
proptest = "1.0"       # 属性测试
```

---

## 📖 学习路径 / Learning Path

建议按以下顺序学习：

1. **二分搜索** - 最简单，理解递归和分治思想
2. **归并排序** - 分治策略的完整应用
3. **快速排序** - 原地排序，理解随机化和分区
4. **LCS** - 动态规划入门
5. **Dijkstra** - 图算法和贪心策略

---

## 🤝 贡献指南 / Contributing

欢迎贡献新的算法实现！请确保：

1. 包含完整的文档注释
2. 添加单元测试和基准测试
3. 遵循Rust代码风格（`cargo fmt`）
4. 通过所有测试（`cargo test`）
5. 链接到对应的形式化文档

---

## 📄 许可证 / License

本项目代码遵循项目整体许可证。

---

**最后更新**: 2025-10-11  
**维护者**: 形式化算法项目团队  
**状态**: 初始版本（5个算法）
