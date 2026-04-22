# 分页问题（Paging / Cache Replacement）

## 概述

分页问题是在线算法中最经典的实际应用之一：给定容量为 $k$ 的缓存和一页请求序列，当请求未命中（page fault）时，需要决定置换哪一页。决策者不知道未来的请求，必须在当前时刻做出不可撤销的决策。

## 问题定义

- **缓存**：容量为 $k$，可存储 $k$ 个不同页面
- **请求序列**：$\sigma = (r_1, r_2, ..., r_n)$，每个 $r_i$ 为页面编号
- **命中（Hit）**：请求的页面已在缓存中，代价 0
- **未命中（Fault）**：请求的页面不在缓存中，需调入，代价 1
- **目标**：最小化总未命中次数

## 离线最优：Belady's MIN

若已知整个请求序列，最优策略是**淘汰最远将来使用**（Farthest-in-Future）的页面。

**定理**（Belady, 1966）：MIN 是最优离线算法。

## 在线算法

### LRU（Least Recently Used）

淘汰最久未被访问的页面。

**竞争比**：$k$（紧界）

**证明概要**：将请求序列按 LRU 的 $k$ 次未命中划分为阶段，每个阶段包含至多 $k$ 个不同页面。OPT 在每个阶段至少 1 次未命中。

### FIFO（First-In-First-Out）

淘汰最早进入缓存的页面。

**竞争比**：$k$

### LFU（Least Frequently Used）

淘汰访问频率最低的页面。

**竞争比**：无界（某些序列下表现极差）

## 下界定理

**定理**：任何确定性在线分页算法的竞争比至少为 $k$。

**证明**：adversary 总是请求当前缓存中不存在的页面（可能，因为缓存只有 $k$ 页，而页面总数 $> k$）。在线算法每次未命中，而 OPT 通过预知未来可控制在每 $k$ 次请求中仅 1 次未命中。

## 随机化改进

### Marker 算法

竞争比：$O(\log k)$

1. 每个阶段开始时，所有页面标记为"未标记"
2. 访问页面时标记为"已标记"
3. 未命中时，从未标记页面中**均匀随机**选择淘汰
4. 若所有页面均已标记，进入下一阶段

## 实际系统

| 系统 | 策略 | 说明 |
|------|------|------|
| CPU Cache | LRU 近似（如 CLOCK）| 硬件实现，开销极低 |
| Linux Page Cache | LRU + 活跃/非活跃列表 | 双队列近似 |
| Redis | LRU / LFU / Random | 可配置策略 |
| Database Buffer Pool | LRU / CLOCK / 2Q | 复杂权衡 |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/data_structures.ts` → `LRU` 相关思想
- Rust: `examples/algorithms/src/lru_cache.rs`
