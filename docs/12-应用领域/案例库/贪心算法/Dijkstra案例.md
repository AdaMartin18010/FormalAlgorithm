# 案例：Dijkstra算法在网络路由中的应用

## 背景

互联网路由协议（如 OSPF、IS-IS）的核心是**最短路径优先（SPF）**计算。Dijkstra算法作为链路状态协议的基础算法，在全球互联网基础设施中每秒被执行数百万次。

## 问题定义

给定自治系统（AS）内的路由器拓扑图：

- 顶点：路由器
- 边权：链路延迟、带宽倒数或管理距离

求从源路由器到所有其他路由器的最优路径。

## Dijkstra在OSPF中的应用

OSPF（Open Shortest Path First）协议：

1. 每个路由器通过链路状态广播（LSA）获取全网拓扑
2. 在本地运行 Dijkstra 算法构建最短路径树（SPT）
3. 生成路由表，选择下一跳

## 优化：优先队列实现

| 实现 | 时间复杂度 | 适用场景 |
|------|-----------|---------|
| 数组扫描 | $O(V^2)$ | 稠密图、小规模网络 |
| 二叉堆 | $O(E \log V)$ | 一般图 |
| 斐波那契堆 | $O(V \log V + E)$ | 理论最优，实际开销大 |

实际路由器通常使用**二叉堆或专用硬件**实现。

## 与BGP的对比

| 特性 | OSPF（Dijkstra） | BGP |
|------|-----------------|-----|
| 范围 | 自治系统内部 | 自治系统之间 |
| 目标 | 最短路径 | 策略导向（商业关系）|
| 算法 | SPF / Dijkstra | 路径向量 |
| 收敛速度 | 快 | 慢（策略复杂）|

## 代码参考

- TypeScript: `examples/algorithms-ts/src/graph.ts` → `dijkstra()`
- Java: `examples/algorithms-java/Dijkstra.java`
- Rust: `examples/algorithms/src/dijkstra.rs`

## 效果评估

- 对 1000 节点的区域网络，Dijkstra 可在毫秒级完成
- 链路状态变化触发增量 SPF（iSPF），将重计算时间降低 50-80%
