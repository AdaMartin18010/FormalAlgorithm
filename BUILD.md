# 构建指南

本项目包含文档和代码两部分，以下是构建和使用指南。

## 文档部分

文档使用Markdown格式，可直接阅读。

### 生成PDF（可选）

```bash
# 使用pandoc生成PDF
cd docs
pandoc README.md -o algorithm-spec.pdf --pdf-engine=xelatex

# 或使用mdbook构建静态站点
cargo install mdbook
mdbook build
mdbook serve  # 本地预览
```

## 代码部分

### Rust代码

```bash
cd examples/algorithms

# 编译
cargo build --release

# 运行测试
cargo test

# 运行基准测试
cargo bench

# 生成文档
cargo doc --open
```

### Go代码

```bash
cd examples/algorithms

# 运行
go run graph.go dp.go sort_advanced.go

# 测试
go test -v
```

### Python代码

```bash
cd examples/algorithms

# 运行
python ml_algorithms.py
python quantum_simulation.py

# 安装依赖
pip install numpy matplotlib
```

### C代码

```bash
cd examples/algorithms

# 编译
gcc sorting.c -o sorting -O2
gcc data_structures.c -o data_structures -O2

# 运行
./sorting
./data_structures
```

## 目录结构说明

```
├── docs/                    # 知识文档
│   ├── 01-基础理论/         # 基础数学理论
│   ├── 09-算法理论/         # 核心算法
│   ├── 习题库/              # 练习题
│   └── ...
│
└── examples/algorithms/     # 代码示例
    ├── src/                 # Rust源码
    │   ├── sorting.rs       # 排序算法
    │   ├── graph_*.rs       # 图算法
    │   └── ...
    ├── *.go                 # Go源码
    ├── *.py                 # Python源码
    └── *.c                  # C源码
```

## 依赖要求

- **Rust**: 1.70+
- **Go**: 1.20+
- **Python**: 3.9+
- **C**: GCC或Clang

## 快速开始

1. **阅读文档**: 从 `docs/README.md` 开始
2. **运行代码**: 查看 `examples/algorithms/src/lib.rs`
3. **练习习题**: 查看 `docs/习题库/`

---

如有问题，请提交Issue。
