# 多语言算法实现 / Multi-Language Algorithm Implementations

## 目录组织

本目录提供算法的多语言实现，采用**双轨组织**模式：

### 轨道1：按算法组织（Rosetta Code模式）⭐ 推荐学习者

```
examples/by-algorithm/
├── lc0001/          # LeetCode 1. Two Sum
│   ├── rust/
│   ├── python/
│   └── go/
└── ...
```

**优势**: 便于横向对比同一算法在不同语言中的实现差异。

### 轨道2：按语言组织（工程模式）⭐ 推荐开发者

```
examples/algorithms-rust/      # Rust 实现
examples/algorithms-python/    # Python 实现
examples/algorithms-go/        # Go 实现
...
```

**优势**: 便于独立构建、测试和部署各语言项目。

## 快速开始

### Rust

```bash
cd examples/algorithms-rust
cargo test
```

### Python

```bash
cd examples/algorithms-python
pytest
```

### Go

```bash
cd examples/algorithms-go
go test ./...
```

### TypeScript

```bash
cd examples/algorithms-ts
npm test
```

## Lean 4 形式化证明

```bash
cd examples/lean_proofs
lake build
```

## 跨语言索引

详见 [CROSS_LANGUAGE_INDEX.md](./CROSS_LANGUAGE_INDEX.md)
