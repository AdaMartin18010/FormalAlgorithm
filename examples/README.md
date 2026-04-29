# 多语言算法实现库

本目录包含 `FormalAlgorithm` 项目的**工程级多语言算法实现**，覆盖 10 种编程语言，提供经典算法与 LeetCode 题目的统一实现与横向对比。

---

## 📁 目录结构

```
examples/
├── README.md                          # ← 本文件（总入口）
├── CROSS_LANGUAGE_INDEX.md            # 跨语言 LeetCode 对照索引
│
├── algorithms-rust/                   # Rust 实现（Cargo 项目）
│   ├── src/classic/                   #   经典算法：排序、图论、DP、数据结构等
│   ├── src/leetcode/                  #   LeetCode 题目实现
│   └── benches/                       #   Criterion 性能基准测试
│
├── algorithms-python/                 # Python 实现
│   ├── src/leetcode/                  #   LeetCode 题目实现
│   ├── src/sorting/                   #   排序算法
│   ├── src/graph/                     #   图算法
│   ├── src/data_structures/           #   数据结构
│   └── tests/                         #   pytest 测试套件
│
├── algorithms-go/                     # Go 实现
│   ├── leetcode/                      #   LeetCode 题目实现
│   ├── *_test.go                      #   内置测试
│   └── go.mod
│
├── algorithms-java/                   # Java 实现（Maven 项目）
│   ├── src/dp/                        #   动态规划
│   ├── src/graph/                     #   图算法
│   ├── src/sorting/                   #   排序算法
│   └── src/test/java/                 #   JUnit 测试
│
├── algorithms-cpp/                    # C++ 实现
│   ├── CMakeLists.txt
│   └── *.cpp                          #   算法实现与测试
│
├── algorithms-ts/                     # TypeScript 实现
│   ├── src/                           #   源码
│   ├── src/tests/                     #   测试
│   └── dist/                          #   编译输出
│
├── algorithms-js/                     # JavaScript 实现
│   └── *.js
│
├── algorithms-c/                      # C 实现
│   └── *.c
│
├── lean_proofs/                       # Lean 形式化证明
│
└── algorithms/                        # ⚠️ 原始混杂目录（已迁移）
    └── README.md                      #   迁移说明
```

> **规范手册**：[docs/项目维护/多语言实现规范手册.md](../docs/项目维护/多语言实现规范手册.md)

---

## 🚀 如何运行测试

### Rust

```bash
cd examples/algorithms-rust
cargo test              # 运行所有单元测试
cargo test leetcode     # 仅运行 LeetCode 模块测试
cargo bench             # 运行性能基准测试
```

### Python

```bash
cd examples/algorithms-python
pytest                  # 运行所有测试
pytest --cov=src        # 带覆盖率报告
```

### Go

```bash
cd examples/algorithms-go
go test ./...           # 运行所有测试
go test -bench=. ./...  # 运行基准测试
```

### Java

```bash
cd examples/algorithms-java
mvn test                # 运行 JUnit 测试
```

### C++

```bash
cd examples/algorithms-cpp
mkdir build && cd build
cmake ..
make
ctest                   # 运行测试（如已配置）
```

### TypeScript

```bash
cd examples/algorithms-ts
npm install
npm test                # 或 npx vitest / jest
```

### JavaScript

```bash
cd examples/algorithms-js
npm test
```

### C

```bash
cd examples/algorithms-c
gcc -o test_runner sorting.c search.c graph.c dynamic.c data_structures.c union_find.c -lm
./test_runner
```

---

## 📊 跨语言覆盖统计

| 语言 | 经典算法 | LeetCode | 测试框架 | 构建工具 |
|------|---------|----------|---------|---------|
| Rust | ✅ 90+ | ✅ 73+ | `cargo test` | Cargo |
| Python | ✅ 20+ | ✅ 80+ | `pytest` | `pyproject.toml` |
| Go | ✅ 15+ | ✅ 66+ | `go test` | Go Modules |
| Java | ✅ 10+ | — | JUnit | Maven |
| C++ | ✅ 12+ | — | 手动 / Catch2 | CMake |
| TypeScript | ✅ 10+ | — | 自定义 | `tsc` + npm |
| JavaScript | ✅ 6+ | — | 自定义 | npm |
| C | ✅ 6+ | — | 手动 | GCC |

> 详细题号对照请查看 [CROSS_LANGUAGE_INDEX.md](./CROSS_LANGUAGE_INDEX.md)

---

## 📝 贡献指南

1. **遵循规范**：所有新实现必须遵守[多语言实现规范手册](../docs/项目维护/多语言实现规范手册.md)
2. **Rosetta Code 模式**：同一算法在不同语言中应放入对应的语言目录，并在 `CROSS_LANGUAGE_INDEX.md` 中登记
3. **必含测试**：每种语言实现必须附带对应的测试文件，覆盖率 ≥ 80%
4. **复杂度标注**：必须在代码注释中标注 `Time Complexity` 和 `Space Complexity`
5. **形式化规约**：推荐包含前置条件、后置条件和循环不变式说明

---

## 🔗 相关文档

| 文档 | 说明 |
|------|------|
| [多语言实现规范手册](../docs/项目维护/多语言实现规范手册.md) | 文件组织、命名、代码风格、测试规范 |
| [CROSS_LANGUAGE_INDEX.md](./CROSS_LANGUAGE_INDEX.md) | LeetCode 跨语言对照索引表 |
| [algorithms-rust/src/leetcode/README.md](./algorithms-rust/src/leetcode/README.md) | Rust LeetCode 实现的详细注释规范 |
| [docs/13-LeetCode算法面试专题](../docs/13-LeetCode算法面试专题/) | 算法范式分析与形式化证明 |

---

## ⚠️ 历史迁移说明

原 `examples/algorithms/` 目录为项目早期创建的混杂目录，同时包含 Rust、Go、Python 文件以及 Cargo 构建产物，已造成维护困难。本次规范化工作已完成以下迁移：

- Rust 代码 → `examples/algorithms-rust/`
- Go 代码 → `examples/algorithms-go/`
- Python 代码 → `examples/algorithms-python/`

详见 `examples/algorithms/README.md` 中的迁移记录。
