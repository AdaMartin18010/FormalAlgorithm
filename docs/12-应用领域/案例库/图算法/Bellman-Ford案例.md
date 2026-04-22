# 案例：Bellman-Ford算法在金融套利检测中的应用

## 背景

外汇市场存在多种货币对及其汇率。当一系列汇率的乘积大于 1 时，就形成了**套利机会**：通过循环兑换可以无风险获利。Bellman-Ford算法可以检测这种负权环。

## 问题建模

### 图构建

- **顶点**：货币（USD、EUR、JPY、GBP...）
- **边**：汇率转换，权重 $w(u,v) = -\log(rate(u,v))$

### 套利条件

汇率乘积 $r_{12} \cdot r_{23} \cdots r_{k1} > 1$ 等价于：

$$-\log(r_{12}) - \log(r_{23}) - \cdots - \log(r_{k1}) < 0$$

即图中存在**负权环**！

## Bellman-Ford检测

1. 引入虚拟源点，向所有货币添加权重为 0 的边
2. 运行 Bellman-Ford
3. 若第 $n$ 轮迭代仍可松弛，则存在负权环 → 存在套利

## 复杂度

- 时间：$O(n^3)$（$n$ 种货币，完全图 $O(n^2)$ 条边）
- 实际外汇市场对约 100 种主要货币，可在毫秒级完成

## 扩展：Floyd-Warshall全源检测

对所有货币对同时检测最短路径，也可用于发现多步套利路径。

## 代码参考

- TypeScript: `examples/algorithms-ts/src/graph.ts` → `bellmanFord()`
- Java: `examples/algorithms-java/Dijkstra.java` 可扩展
- Go: `examples/algorithms-go/graph.go`

## 实际约束

- 真实市场套利窗口极短（毫秒级）
- 需考虑交易手续费和滑点
- 高频交易系统使用专用硬件加速最短路径计算
