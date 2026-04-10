# FormalAlgorithm 开发环境 Dockerfile
# 基于 Rust 官方镜像构建

FROM rust:1.75-slim-bookworm as base

# 设置工作目录
WORKDIR /workspace

# 安装系统依赖
RUN apt-get update && apt-get install -y --no-install-recommends \
    # 基础工具
    git \
    curl \
    wget \
    vim \
    nano \
    # 构建工具
    build-essential \
    cmake \
    pkg-config \
    # 文档工具
    pandoc \
    # 代码分析工具
    valgrind \
    gdb \
    # 其他实用工具
    tree \
    htop \
    # 清理
    && rm -rf /var/lib/apt/lists/*

# 安装 Rust 工具链组件
RUN rustup component add \
    rustfmt \
    clippy \
    rust-src \
    rust-docs \
    llvm-tools-preview

# 安装常用的 Cargo 工具
RUN cargo install --locked \
    cargo-watch \
    cargo-tarpaulin \
    cargo-audit \
    cargo-tree \
    cargo-outdated \
    cargo-edit \
    mdbook \
    mdbook-linkcheck \
    2>/dev/null || true

# 开发阶段
FROM base as development

# 复制项目文件
COPY . /workspace/

# 设置环境变量
ENV RUST_BACKTRACE=1
ENV CARGO_TERM_COLOR=always

# 构建项目（用于缓存依赖）
RUN cd /workspace/examples/algorithms && \
    cargo fetch && \
    cargo build 2>/dev/null || true

# 暴露常用端口（用于文档服务器等）
EXPOSE 3000 8080

# 默认命令
CMD ["/bin/bash"]

# 生产构建阶段
FROM base as production

# 只复制必要文件
COPY examples/algorithms /workspace/examples/algorithms/
COPY docs /workspace/docs/
COPY README.md LICENSE /workspace/

# 构建发布版本
RUN cd /workspace/examples/algorithms && \
    cargo build --release

# 设置非root用户
RUN useradd -m -u 1000 algorithm && \
    chown -R algorithm:algorithm /workspace
USER algorithm

CMD ["/bin/bash"]

# 文档服务阶段
FROM base as docs

COPY . /workspace/

# 安装 Node.js（用于某些文档工具）
RUN curl -fsSL https://deb.nodesource.com/setup_20.x | bash - && \
    apt-get install -y nodejs && \
    npm install -g cspell markdownlint-cli

WORKDIR /workspace

EXPOSE 3000

CMD ["mdbook", "serve", "--hostname", "0.0.0.0", "--port", "3000"]
