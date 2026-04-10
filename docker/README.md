# FormalAlgorithm Docker 开发环境

本目录包含 FormalAlgorithm 项目的 Docker 配置文件，提供统一的开发、测试和文档服务环境。

## 目录结构

```
docker/
├── Dockerfile          # 多阶段构建的 Docker 镜像定义
├── docker-compose.yml  # 多服务编排配置
└── README.md          # 本文件
```

## 快速开始

### 1. 安装 Docker 和 Docker Compose

- [Docker 安装指南](https://docs.docker.com/get-docker/)
- [Docker Compose 安装指南](https://docs.docker.com/compose/install/)

### 2. 构建开发环境

```bash
# 进入项目根目录
cd G:\_src\FormalAlgorithm

# 构建开发镜像
docker-compose -f docker/docker-compose.yml build dev
```

### 3. 启动开发环境

```bash
# 启动并进入开发容器
docker-compose -f docker/docker-compose.yml run --rm dev

# 在容器内可以执行各种 cargo 命令
cargo build
cargo test
cargo run
```

## 服务说明

### 开发环境 (dev)

完整的 Rust 开发环境，包含所有必要的工具和依赖。

```bash
# 启动交互式开发环境
docker-compose -f docker/docker-compose.yml run --rm dev

# 在后台运行
docker-compose -f docker/docker-compose.yml up -d dev

# 执行单次命令
docker-compose -f docker/docker-compose.yml run --rm dev cargo test
```

**包含的工具：**
- Rust 1.75+ 工具链
- rustfmt, clippy, rust-src
- cargo-watch, cargo-tarpaulin, cargo-audit
- mdbook, mdbook-linkcheck
- git, vim, gdb, valgrind

### 文档服务 (docs)

启动文档服务器，用于预览文档。

```bash
# 启动文档服务（访问 http://localhost:3000）
docker-compose -f docker/docker-compose.yml up docs

# 后台运行
docker-compose -f docker/docker-compose.yml up -d docs
```

### 测试服务 (test)

运行完整的测试套件。

```bash
# 运行所有测试
docker-compose -f docker/docker-compose.yml --profile test run --rm test

# 带输出运行
docker-compose -f docker/docker-compose.yml --profile test run --rm test cargo test -- --nocapture
```

### 代码检查 (lint)

运行代码格式检查和 clippy 检查。

```bash
# 运行 lint 检查
docker-compose -f docker/docker-compose.yml --profile lint run --rm lint
```

### 覆盖率报告 (coverage)

生成代码覆盖率报告。

```bash
# 生成覆盖率报告
docker-compose -f docker/docker-compose.yml --profile coverage run --rm coverage

# 报告将保存在 coverage/ 目录
```

## 常用命令

### 构建

```bash
# 构建所有服务
docker-compose -f docker/docker-compose.yml build

# 构建特定服务
docker-compose -f docker/docker-compose.yml build dev
```

### 运行

```bash
# 进入开发环境
docker-compose -f docker/docker-compose.yml run --rm dev

# 运行测试
docker-compose -f docker/docker-compose.yml --profile test run --rm test

# 生成覆盖率报告
docker-compose -f docker/docker-compose.yml --profile coverage run --rm coverage
```

### 清理

```bash
# 停止所有服务
docker-compose -f docker/docker-compose.yml down

# 停止并删除卷
docker-compose -f docker/docker-compose.yml down -v

# 清理未使用的镜像和缓存
docker system prune -f
```

## Dockerfile 阶段说明

| 阶段 | 用途 | 说明 |
|------|------|------|
| base | 基础镜像 | 安装系统依赖和 Rust 工具 |
| development | 开发环境 | 包含完整开发工具，挂载源代码 |
| production | 生产环境 | 仅包含构建好的二进制文件 |
| docs | 文档服务 | 用于预览和构建文档 |

## 数据持久化

使用 Docker Volume 持久化以下数据：

- `cargo-cache`: Cargo 注册表缓存，加速依赖下载
- `target-cache`: 编译产物缓存，加速重新构建
- `coverage-reports`: 覆盖率报告输出目录

## 故障排除

### 权限问题

如果在 Linux 上遇到文件权限问题：

```bash
# 修改容器内文件所有者
sudo chown -R $(id -u):$(id -g) .
```

### 内存不足

构建时内存不足，可以调整 Docker 内存限制或添加 swap：

```bash
# 创建 swap 文件
sudo fallocate -l 4G /swapfile
sudo chmod 600 /swapfile
sudo mkswap /swapfile
sudo swapon /swapfile
```

### 网络问题

如果下载依赖缓慢，可以配置镜像：

```bash
# 创建 cargo 配置目录
mkdir -p ~/.cargo

# 配置国内镜像
cat > ~/.cargo/config <<EOF
[source.crates-io]
replace-with = 'rsproxy'

[source.rsproxy]
registry = "https://rsproxy.cn/crates.io-index"
EOF
```

## 高级用法

### 自定义构建参数

```bash
# 使用特定 Rust 版本
docker build --build-arg RUST_VERSION=1.70 -f docker/Dockerfile -t formal-algorithm:dev .
```

### 多平台构建

```bash
# 设置 buildx
docker buildx create --use

# 构建多平台镜像
docker buildx build --platform linux/amd64,linux/arm64 -f docker/Dockerfile -t formal-algorithm:latest .
```

## 相关链接

- [项目主页](../README.md)
- [文档目录](../docs/README.md)
- [CI 配置](../.github/workflows/ci.yml)
