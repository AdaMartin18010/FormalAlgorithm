# 随机游走在 PageRank 中的应用

## 概述

PageRank 是 Google 创始人 Larry Page 和 Sergey Brin 提出的网页重要性排序算法。它将互联网建模为有向图，通过模拟**随机游走**（Random Walk）来估计每个页面的"重要性"。

## 基本模型

### 随机冲浪者（Random Surfer）

想象一个用户在网页间随机点击链接：

- 在页面 $i$ 时，均匀随机选择一条出链跳转
- 若页面无出链（dangling node），随机跳转到任意页面

长期访问频率即为页面的 PageRank 值。

## 数学形式化

### 转移矩阵

设互联网有 $n$ 个页面，定义转移矩阵 $M$：

$$M_{ij} = \begin{cases} \frac{1}{L(j)} & \text{若 } j \to i \text{ 有链接} \\ 0 & \text{否则} \end{cases}$$

其中 $L(j)$ 为页面 $j$ 的出链数。

### PageRank 向量

PageRank 向量 $PR$ 满足：

$$PR = d \cdot M \cdot PR + \frac{1-d}{n} \cdot \mathbf{1}$$

其中 $d \approx 0.85$ 为**阻尼系数**（damping factor），表示用户继续点击的概率；$1-d$ 为随机跳转概率。

### 幂迭代法

```
PR_0 = [1/n, 1/n, ..., 1/n]
repeat:
    PR_{k+1} = d * M * PR_k + (1-d)/n
until ||PR_{k+1} - PR_k|| < epsilon
```

收敛速度取决于 $M$ 的第二特征值，通常 50-100 次迭代即可收敛。

## 随机游走的解释

PageRank 等价于在图上进行带**重启**（restart）的随机游走：

- 以概率 $d$ 沿边游走
- 以概率 $1-d$ 随机重启到任意节点

长期稳态分布即为 PageRank。

## 扩展：个性化 PageRank

将均匀重启改为从特定节点（或节点集合）重启：

$$PR = d \cdot M \cdot PR + (1-d) \cdot \mathbf{v}$$

其中 $\mathbf{v}$ 为个性化偏好向量。用于推荐系统和局部社区发现。

## 代码参考

- TypeScript: `examples/algorithms-ts/src/graph.ts`（图结构基础）
- Rust: `examples/algorithms/src/`（可扩展）

## 效果评估

- 对 10 亿页面规模的图，分布式幂迭代可在数小时内收敛
- PageRank 是 Google 早期核心算法，至今仍为排名信号之一
