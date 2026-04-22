# 案例：A*搜索在游戏AI寻路与地图导航中的应用

## 背景

在电子游戏、地图导航和机器人路径规划中，需要找到从起点到终点的**最短可行路径**。A*（A-Star）算法通过引入启发式函数，将搜索导向目标方向，在大多数实际场景中远快于 Dijkstra 和 BFS。

## 问题定义

- **图**：网格图或道路网络，边有权值（距离、时间、燃料消耗）
- **起点** $s$，**终点** $t$
- **目标**：找到 $s \to t$ 的最短路径

## A* 核心

### 评估函数

$$f(v) = g(v) + h(v)$$

- $g(v)$：从起点到 $v$ 的实际代价（Dijkstra 部分）
- $h(v)$：从 $v$ 到终点的启发式估计

### 启发式要求

- **可采纳（Admissible）**：$h(v) \leq h^*(v)$（真实最短距离）
  - 保证 A* 找到最优解
- **一致（Consistent）**：$h(u) \leq c(u,v) + h(v)$
  - 保证首次访问即最优，无需重新更新

### 经典启发式

| 场景 | 启发式 | 可采纳性 |
|------|--------|---------|
| 网格（4方向）| 曼哈顿距离 | ✅ |
| 网格（8方向）| 切比雪夫距离 | ✅ |
| 地理坐标 | 大圆距离（Haversine）| ✅ |
| 欧几里得空间 | 欧几里得距离 | ✅ |

## 与 Dijkstra、BFS 的对比

| 算法 | 搜索范围 | 最优性 | 适用场景 |
|------|---------|--------|---------|
| BFS | 全图扩展 | ✅ 无权图 | 无权网格 |
| Dijkstra | 全图扩展 | ✅ 有权图 | 道路网络（无启发式信息）|
| **A*** | **目标导向** | **✅ 可采纳时** | **游戏、导航** |
| 贪心最佳优先 | 目标导向 | ❌ 不保证 | 快速但不精确 |

## 实际应用

### 游戏开发

- **即时战略**（StarCraft、Age of Empires）：单位移动
- **角色扮演**（The Witcher、Zelda）：NPC 寻路
- **塔防/策略**：敌人路径规划
- **Unity/Unreal**：内置 NavMesh + A* 寻路

### 地图导航

- Google Maps、高德地图的路径规划
- 考虑实时交通的加权 A*（Dynamic A*）
- 分层路由：高速公路优先 + 局部 A*

### 机器人路径规划

- 自动驾驶车辆的路径规划（结合 RRT*）
- 仓库机器人（Amazon Kiva）的调度
- 无人机航路规划

### 变体算法

| 变体 | 特点 |
|------|------|
| D* Lite | 动态环境，局部 replanning |
| Theta* | 允许非网格直线路径 |
| Jump Point Search | 网格对称性剪枝，快 10x |
| HPA* | 分层抽象 + 局部 A* |

## 代码参考

- TypeScript: `examples/algorithms-ts/src/graph.ts` → `astar()`
- Rust: `examples/algorithms/src/graph_algorithms/astar.rs`
- Java: `examples/algorithms-java/GraphAlgorithms.java` → `astar()`
- Go: `examples/algorithms-go/graph.go` → `AStar()`

## 效果评估

- 在 1000x1000 网格上，A* 通常访问 < 5% 节点（vs Dijkstra 的 50%+）
- Jump Point Search 在开放网格上快 10-30 倍
- 现代游戏引擎中，A* 寻路 < 1ms/帧
