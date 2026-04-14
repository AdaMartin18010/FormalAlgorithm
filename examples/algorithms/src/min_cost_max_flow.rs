//! 最小费用最大流 (Minimum Cost Maximum Flow)
//!
//! 最小费用最大流问题：在流网络中找到从源点到汇点的最大流，使得总费用最小。
//! 每条边有容量限制和单位流量费用。
//!
//! # 算法原理
//! 使用SPFA（Shortest Path Faster Algorithm）或Dijkstra算法寻找最短路（最小费用路），
//! 然后沿最短路增广，直到不存在增广路为止。
//!
//! # 算法流程
//! 1. 初始化：流量为0，费用为0
//! 2. 使用SPFA/Dijkstra寻找从源点到汇点的最短路（考虑费用）
//! 3. 如果存在最短路，沿该路径增广
//! 4. 重复步骤2-3直到不存在增广路
//!
//! # 时间复杂度
//! - SPFA版本: O(V · E · max_flow) 最坏情况，实际通常很快
//! - Dijkstra版本: O(max_flow · E · log V) 使用势能优化
//! - 空间: O(V + E)
//!
//! # 应用场景
//! - 运输问题：最小成本运输
//! - 任务分配：最优人员分配
//! - 网络设计：最小成本网络流

use std::collections::{HashMap, VecDeque};
use std::hash::Hash;

/// 边结构体
#[derive(Clone, Debug)]
struct Edge {
    /// 目标节点
    to: usize,
    /// 反向边索引
    rev: usize,
    /// 剩余容量
    capacity: i64,
    /// 单位流量费用
    cost: i64,
    /// 原始容量（用于获取流量）
    original_capacity: i64,
}

/// 最小费用最大流求解器
pub struct MinCostMaxFlow {
    /// 图的邻接表表示
    graph: Vec<Vec<Edge>>,
    /// 节点数量
    n: usize,
}

/// 最小费用最大流结果
#[derive(Debug, Clone)]
pub struct MCMFResult {
    /// 最大流量
    pub max_flow: i64,
    /// 最小费用
    pub min_cost: i64,
    /// 每单位流量的费用明细
    pub flow_cost_details: Vec<(i64, i64)>, // (流量增量, 当前单位费用)
}

impl MinCostMaxFlow {
    /// 创建新的最小费用最大流求解器
    ///
    /// # 参数
    /// - `n`: 节点数量（节点编号为 0 到 n-1）
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::MinCostMaxFlow;
    /// let mcmf = MinCostMaxFlow::new(4);
    /// ```
    pub fn new(n: usize) -> Self {
        MinCostMaxFlow {
            graph: vec![Vec::new(); n],
            n,
        }
    }

    /// 添加边
    ///
    /// # 参数
    /// - `from`: 起始节点
    /// - `to`: 目标节点
    /// - `capacity`: 容量
    /// - `cost`: 单位流量费用
    ///
    /// # 说明
    /// 自动添加反向边，用于残量网络
    pub fn add_edge(&mut self, from: usize, to: usize, capacity: i64, cost: i64) {
        let from_len = self.graph[from].len();
        let to_len = self.graph[to].len();

        // 正向边
        self.graph[from].push(Edge {
            to,
            rev: to_len,
            capacity,
            cost,
            original_capacity: capacity,
        });

        // 反向边（初始容量为0，费用为负）
        self.graph[to].push(Edge {
            to: from,
            rev: from_len,
            capacity: 0,
            cost: -cost,
            original_capacity: 0,
        });
    }

    /// 使用SPFA算法求解最小费用最大流
    ///
    /// # 参数
    /// - `source`: 源点
    /// - `sink`: 汇点
    ///
    /// # 返回值
    /// 返回 `MCMFResult`，包含最大流量和最小费用
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::MinCostMaxFlow;
    /// let mut mcmf = MinCostMaxFlow::new(4);
    /// mcmf.add_edge(0, 1, 3, 1);  // 0->1, 容量3, 费用1
    /// mcmf.add_edge(0, 2, 2, 2);  // 0->2, 容量2, 费用2
    /// mcmf.add_edge(1, 2, 1, 1);  // 1->2, 容量1, 费用1
    /// mcmf.add_edge(1, 3, 3, 3);  // 1->3, 容量3, 费用3
    /// mcmf.add_edge(2, 3, 2, 1);  // 2->3, 容量2, 费用1
    ///
    /// let result = mcmf.min_cost_flow_spfa(0, 3);
    /// assert_eq!(result.max_flow, 5);
    /// ```
    pub fn min_cost_flow_spfa(&mut self, source: usize, sink: usize) -> MCMFResult {
        let mut max_flow = 0i64;
        let mut min_cost = 0i64;
        let mut flow_cost_details = Vec::new();

        loop {
            // SPFA寻找最短路
            let (dist, parent_vertex, parent_edge) = self.spfa(source);

            // 如果汇点不可达，结束
            if dist[sink] == i64::MAX {
                break;
            }

            // 找到增广路径上的最小残量
            let mut flow = i64::MAX;
            let mut v = sink;
            while v != source {
                let u = parent_vertex[v];
                let e = &self.graph[u][parent_edge[v]];
                flow = flow.min(e.capacity);
                v = u;
            }

            // 增广
            v = sink;
            while v != source {
                let u = parent_vertex[v];
                let e_idx = parent_edge[v];

                // 更新正向边
                self.graph[u][e_idx].capacity -= flow;
                // 更新反向边
                let rev_idx = self.graph[u][e_idx].rev;
                self.graph[v][rev_idx].capacity += flow;

                v = u;
            }

            max_flow += flow;
            min_cost += flow * dist[sink];
            flow_cost_details.push((flow, dist[sink]));
        }

        MCMFResult {
            max_flow,
            min_cost,
            flow_cost_details,
        }
    }

    /// SPFA算法（Shortest Path Faster Algorithm）
    ///
    /// 用于在存在负权边的情况下寻找最短路
    fn spfa(&self, source: usize) -> (Vec<i64>, Vec<usize>, Vec<usize>) {
        let n = self.n;
        let mut dist = vec![i64::MAX; n];
        let mut in_queue = vec![false; n];
        let mut parent_vertex = vec![0; n]; // 记录前驱节点
        let mut parent_edge = vec![0; n];   // 记录通过哪条边到达

        dist[source] = 0;
        let mut queue = VecDeque::new();
        queue.push_back(source);
        in_queue[source] = true;

        while let Some(u) = queue.pop_front() {
            in_queue[u] = false;

            for (i, edge) in self.graph[u].iter().enumerate() {
                if edge.capacity > 0 && dist[u] + edge.cost < dist[edge.to] {
                    dist[edge.to] = dist[u] + edge.cost;
                    parent_vertex[edge.to] = u;
                    parent_edge[edge.to] = i;

                    if !in_queue[edge.to] {
                        queue.push_back(edge.to);
                        in_queue[edge.to] = true;
                    }
                }
            }
        }

        (dist, parent_vertex, parent_edge)
    }

    /// 使用Dijkstra算法求解最小费用最大流（带势能优化）
    ///
    /// # 参数
    /// - `source`: 源点
    /// - `sink`: 汇点
    ///
    /// # 说明
    /// 使用势能函数（Johnson算法思想）将负权边转化为非负权边，
    /// 然后使用Dijkstra算法，效率更高
    pub fn min_cost_flow_dijkstra(&mut self, source: usize, sink: usize) -> MCMFResult {
        let mut max_flow = 0i64;
        let mut min_cost = 0i64;
        let mut flow_cost_details = Vec::new();

        // 势能数组（用于处理负权边）
        let mut potential = vec![0i64; self.n];

        loop {
            // Dijkstra寻找最短路（使用势能调整后的费用）
            let (dist, parent_vertex, parent_edge) =
                self.dijkstra_with_potential(source, &potential);

            // 如果汇点不可达，结束
            if dist[sink] == i64::MAX {
                break;
            }

            // 更新势能
            for i in 0..self.n {
                if dist[i] < i64::MAX {
                    potential[i] += dist[i];
                }
            }

            // 找到增广路径上的最小残量
            let mut flow = i64::MAX;
            let mut v = sink;
            while v != source {
                let u = parent_vertex[v];
                let e = &self.graph[u][parent_edge[v]];
                flow = flow.min(e.capacity);
                v = u;
            }

            // 增广
            v = sink;
            while v != source {
                let u = parent_vertex[v];
                let e_idx = parent_edge[v];

                self.graph[u][e_idx].capacity -= flow;
                let rev_idx = self.graph[u][e_idx].rev;
                self.graph[v][rev_idx].capacity += flow;

                v = u;
            }

            max_flow += flow;
            min_cost += flow * potential[sink]; // 使用势能计算实际费用
            flow_cost_details.push((flow, potential[sink]));
        }

        MCMFResult {
            max_flow,
            min_cost,
            flow_cost_details,
        }
    }

    /// 带势能的Dijkstra算法
    fn dijkstra_with_potential(
        &self,
        source: usize,
        potential: &[i64],
    ) -> (Vec<i64>, Vec<usize>, Vec<usize>) {
        let n = self.n;
        let mut dist = vec![i64::MAX; n];
        let mut visited = vec![false; n];
        let mut parent_vertex = vec![0; n];
        let mut parent_edge = vec![0; n];

        dist[source] = 0;

        for _ in 0..n {
            // 找到未访问的最小距离节点
            let mut u = n;
            let mut min_dist = i64::MAX;
            for i in 0..n {
                if !visited[i] && dist[i] < min_dist {
                    min_dist = dist[i];
                    u = i;
                }
            }

            if u == n {
                break;
            }

            visited[u] = true;

            // 松弛邻接边
            for (i, edge) in self.graph[u].iter().enumerate() {
                if edge.capacity > 0 && !visited[edge.to] {
                    // 使用调整后的费用: cost + potential[u] - potential[edge.to]
                    let adjusted_cost = edge.cost + potential[u] - potential[edge.to];
                    if dist[u] + adjusted_cost < dist[edge.to] {
                        dist[edge.to] = dist[u] + adjusted_cost;
                        parent_vertex[edge.to] = u;
                        parent_edge[edge.to] = i;
                    }
                }
            }
        }

        (dist, parent_vertex, parent_edge)
    }

    /// 获取指定边的当前流量
    ///
    /// # 参数
    /// - `from`: 起始节点
    /// - `edge_idx`: 边在邻接表中的索引
    ///
    /// # 返回值
    /// 返回该边的当前流量
    pub fn get_flow(&self, from: usize, edge_idx: usize) -> i64 {
        let edge = &self.graph[from][edge_idx];
        edge.original_capacity - edge.capacity
    }

    /// 获取所有边的流量分布
    ///
    /// # 返回值
    /// 返回 (from, to, flow, capacity, cost) 的列表
    pub fn get_flow_distribution(&self) -> Vec<(usize, usize, i64, i64, i64)> {
        let mut result = Vec::new();

        for from in 0..self.n {
            for (idx, edge) in self.graph[from].iter().enumerate() {
                // 只输出正向边（原始容量大于0的边）
                if edge.original_capacity > 0 {
                    let flow = edge.original_capacity - edge.capacity;
                    result.push((from, edge.to, flow, edge.original_capacity, edge.cost));
                }
            }
        }

        result
    }
}

impl MCMFResult {
    /// 获取单位流量的平均费用
    pub fn average_cost(&self) -> f64 {
        if self.max_flow == 0 {
            0.0
        } else {
            self.min_cost as f64 / self.max_flow as f64
        }
    }

    /// 打印详细结果
    pub fn print_details(&self) {
        println!("=== 最小费用最大流结果 ===");
        println!("最大流量: {}", self.max_flow);
        println!("最小费用: {}", self.min_cost);
        println!("平均单位费用: {:.2}", self.average_cost());
        println!("\n增广过程:");
        for (i, (flow, cost)) in self.flow_cost_details.iter().enumerate() {
            println!("  第{}轮: 流量={}, 单位费用={}, 总费用={}",
                     i + 1, flow, cost, flow * cost);
        }
    }
}

/// 辅助函数：快速求解最小费用最大流（SPFA版本）
pub fn min_cost_max_flow_spfa(
    n: usize,
    edges: &[(usize, usize, i64, i64)], // (from, to, capacity, cost)
    source: usize,
    sink: usize,
) -> MCMFResult {
    let mut mcmf = MinCostMaxFlow::new(n);
    for &(from, to, capacity, cost) in edges {
        mcmf.add_edge(from, to, capacity, cost);
    }
    mcmf.min_cost_flow_spfa(source, sink)
}

/// 辅助函数：快速求解最小费用最大流（Dijkstra版本）
pub fn min_cost_max_flow_dijkstra(
    n: usize,
    edges: &[(usize, usize, i64, i64)],
    source: usize,
    sink: usize,
) -> MCMFResult {
    let mut mcmf = MinCostMaxFlow::new(n);
    for &(from, to, capacity, cost) in edges {
        mcmf.add_edge(from, to, capacity, cost);
    }
    mcmf.min_cost_flow_dijkstra(source, sink)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_flow() {
        // 基本测试用例
        // 0 -> 1 -> 3
        // 0 -> 2 -> 3
        // 1 -> 2
        let mut mcmf = MinCostMaxFlow::new(4);
        mcmf.add_edge(0, 1, 3, 1);
        mcmf.add_edge(0, 2, 2, 2);
        mcmf.add_edge(1, 2, 1, 1);
        mcmf.add_edge(1, 3, 3, 3);
        mcmf.add_edge(2, 3, 2, 1);

        let result = mcmf.min_cost_flow_spfa(0, 3);
        assert_eq!(result.max_flow, 5);
        assert_eq!(result.min_cost, 18); // 0->1->3: 3*(1+3)=12; 0->2->3: 2*(2+1)=6; total=18
    }

    #[test]
    fn test_spfa_vs_dijkstra() {
        let edges = vec![
            (0, 1, 3, 1),
            (0, 2, 2, 2),
            (1, 2, 1, 1),
            (1, 3, 3, 3),
            (2, 3, 2, 1),
        ];

        let result_spfa = min_cost_max_flow_spfa(4, &edges, 0, 3);
        let result_dijkstra = min_cost_max_flow_dijkstra(4, &edges, 0, 3);

        assert_eq!(result_spfa.max_flow, result_dijkstra.max_flow);
        assert_eq!(result_spfa.min_cost, result_dijkstra.min_cost);
    }

    #[test]
    fn test_no_flow() {
        // 没有路径的情况
        let mut mcmf = MinCostMaxFlow::new(3);
        mcmf.add_edge(0, 1, 5, 1);
        // 2是孤立点

        let result = mcmf.min_cost_flow_spfa(0, 2);
        assert_eq!(result.max_flow, 0);
        assert_eq!(result.min_cost, 0);
    }

    #[test]
    fn test_single_edge() {
        let mut mcmf = MinCostMaxFlow::new(2);
        mcmf.add_edge(0, 1, 10, 5);

        let result = mcmf.min_cost_flow_spfa(0, 1);
        assert_eq!(result.max_flow, 10);
        assert_eq!(result.min_cost, 50);
    }

    #[test]
    fn test_multiple_paths() {
        // 多条路径的情况
        // 0 -> 1 -> 3 (容量5, 费用2+3=5)
        // 0 -> 2 -> 3 (容量3, 费用1+2=3)
        let mut mcmf = MinCostMaxFlow::new(4);
        mcmf.add_edge(0, 1, 5, 2);
        mcmf.add_edge(0, 2, 3, 1);
        mcmf.add_edge(1, 3, 5, 3);
        mcmf.add_edge(2, 3, 3, 2);

        let result = mcmf.min_cost_flow_spfa(0, 3);
        assert_eq!(result.max_flow, 8); // 5 + 3
        assert_eq!(result.min_cost, 34); // 优先使用便宜的路径
    }

    #[test]
    fn test_flow_distribution() {
        let mut mcmf = MinCostMaxFlow::new(3);
        mcmf.add_edge(0, 1, 5, 2);
        mcmf.add_edge(1, 2, 3, 3);

        let result = mcmf.min_cost_flow_spfa(0, 2);
        assert_eq!(result.max_flow, 3);
        assert_eq!(result.min_cost, 15); // 3 * (2+3)

        let distribution = mcmf.get_flow_distribution();
        assert_eq!(distribution.len(), 2);
        assert_eq!(distribution[0].2, 3); // 流量为3
        assert_eq!(distribution[1].2, 3);
    }

    #[test]
    fn test_negative_cost() {
        // 测试负费用（使用Dijkstra版本需要势能）
        let mut mcmf = MinCostMaxFlow::new(3);
        mcmf.add_edge(0, 1, 5, -2); // 负费用
        mcmf.add_edge(1, 2, 5, 3);

        let result = mcmf.min_cost_flow_spfa(0, 2);
        assert_eq!(result.max_flow, 5);
        assert_eq!(result.min_cost, 5); // 5 * (-2 + 3) = 5
    }

    #[test]
    fn test_assignment_problem() {
        // 分配问题：3个工人，3个任务
        // 源点 -> 工人 -> 任务 -> 汇点
        // 结构：0(源点), 1-3(工人), 4-6(任务), 7(汇点)
        let mut mcmf = MinCostMaxFlow::new(8);

        // 源点到工人
        for i in 1..=3 {
            mcmf.add_edge(0, i, 1, 0);
        }

        // 工人到任务（费用为工作效率的倒数）
        let costs = [
            [3, 2, 4],  // 工人1
            [2, 3, 1],  // 工人2
            [4, 1, 3],  // 工人3
        ];

        for i in 0..3 {
            for j in 0..3 {
                mcmf.add_edge(i + 1, j + 4, 1, costs[i][j]);
            }
        }

        // 任务到汇点
        for j in 0..3 {
            mcmf.add_edge(j + 4, 7, 1, 0);
        }

        let result = mcmf.min_cost_flow_spfa(0, 7);
        assert_eq!(result.max_flow, 3); // 分配3个任务
        // 最优分配: 工人1->任务1(3), 工人2->任务3(1), 工人3->任务2(1) = 5
        // 修正说明：原期望值 7 有误，实际最小费用为 5
        assert_eq!(result.min_cost, 5);
    }

    #[test]
    fn test_large_capacity() {
        let mut mcmf = MinCostMaxFlow::new(2);
        mcmf.add_edge(0, 1, 1_000_000, 1);

        let result = mcmf.min_cost_flow_spfa(0, 1);
        assert_eq!(result.max_flow, 1_000_000);
        assert_eq!(result.min_cost, 1_000_000);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn transportation_problem() {
        println!("\n=== 运输问题示例 ===");

        // 两个工厂，三个仓库
        // 0: 源点, 1-2: 工厂, 3-5: 仓库, 6: 汇点
        let mut mcmf = MinCostMaxFlow::new(7);

        // 工厂产能
        mcmf.add_edge(0, 1, 100, 0);  // 工厂1产能100
        mcmf.add_edge(0, 2, 150, 0);  // 工厂2产能150

        // 运输费用
        mcmf.add_edge(1, 3, 50, 3);   // 工厂1到仓库1: 50单位, 费用3
        mcmf.add_edge(1, 4, 50, 2);   // 工厂1到仓库2: 50单位, 费用2
        mcmf.add_edge(1, 5, 50, 4);   // 工厂1到仓库3: 50单位, 费用4
        mcmf.add_edge(2, 3, 50, 2);   // 工厂2到仓库1: 50单位, 费用2
        mcmf.add_edge(2, 4, 50, 3);   // 工厂2到仓库2: 50单位, 费用3
        mcmf.add_edge(2, 5, 100, 1);  // 工厂2到仓库3: 100单位, 费用1

        // 仓库需求
        mcmf.add_edge(3, 6, 80, 0);   // 仓库1需求80
        mcmf.add_edge(4, 6, 70, 0);   // 仓库2需求70
        mcmf.add_edge(5, 6, 100, 0);  // 仓库3需求100

        let result = mcmf.min_cost_flow_spfa(0, 6);

        println!("最大运输量: {}", result.max_flow);
        println!("最小运输费用: {}", result.min_cost);
        println!("平均单位费用: {:.2}", result.average_cost());

        println!("\n运输方案:");
        for (from, to, flow, capacity, cost) in mcmf.get_flow_distribution() {
            if flow > 0 && from > 0 && from < 6 && to > 0 && to < 6 {
                let node_name = |n| match n {
                    1 => "工厂1",
                    2 => "工厂2",
                    3 => "仓库1",
                    4 => "仓库2",
                    5 => "仓库3",
                    _ => "?",
                };
                println!("  {} -> {}: {}/{} 单位, 单位费用 {}, 总费用 {}",
                         node_name(from), node_name(to),
                         flow, capacity, cost, flow * cost);
            }
        }
    }

    #[test]
    fn network_optimization() {
        println!("\n=== 网络流量优化示例 ===");

        let mut mcmf = MinCostMaxFlow::new(6);

        // 构建网络拓扑
        mcmf.add_edge(0, 1, 10, 2);
        mcmf.add_edge(0, 2, 15, 3);
        mcmf.add_edge(1, 3, 8, 4);
        mcmf.add_edge(1, 4, 5, 1);
        mcmf.add_edge(2, 3, 10, 2);
        mcmf.add_edge(2, 4, 12, 3);
        mcmf.add_edge(3, 5, 15, 2);
        mcmf.add_edge(4, 5, 20, 1);

        // 比较两种算法的结果
        let mut mcmf_spfa = MinCostMaxFlow::new(6);
        let mut mcmf_dijkstra = MinCostMaxFlow::new(6);

        let edges = [
            (0, 1, 10, 2),
            (0, 2, 15, 3),
            (1, 3, 8, 4),
            (1, 4, 5, 1),
            (2, 3, 10, 2),
            (2, 4, 12, 3),
            (3, 5, 15, 2),
            (4, 5, 20, 1),
        ];

        for &(from, to, cap, cost) in &edges {
            mcmf_spfa.add_edge(from, to, cap, cost);
            mcmf_dijkstra.add_edge(from, to, cap, cost);
        }

        let result_spfa = mcmf_spfa.min_cost_flow_spfa(0, 5);
        let result_dijkstra = mcmf_dijkstra.min_cost_flow_dijkstra(0, 5);

        println!("SPFA算法:");
        println!("  最大流: {}, 最小费用: {}",
                 result_spfa.max_flow, result_spfa.min_cost);

        println!("Dijkstra算法:");
        println!("  最大流: {}, 最小费用: {}",
                 result_dijkstra.max_flow, result_dijkstra.min_cost);

        assert_eq!(result_spfa.max_flow, result_dijkstra.max_flow);
        assert_eq!(result_spfa.min_cost, result_dijkstra.min_cost);
    }
}
