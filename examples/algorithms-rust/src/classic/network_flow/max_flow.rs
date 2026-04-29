//! 最大流算法
//! 
//! 实现:
//! - Ford-Fulkerson (DFS增广路)
//! - Edmonds-Karp (BFS增广路)
//! - Dinic算法
//! 
//! 对标: CLRS 26 / MIT 6.046

use std::collections::{VecDeque, HashMap};
use std::cmp::min;

/// 流网络中的边
#[derive(Clone, Debug)]
pub struct Edge {
    pub to: usize,
    pub rev: usize,  // 反向边索引
    pub capacity: i64,
    pub flow: i64,
}

/// 最大流求解器
pub struct MaxFlow {
    n: usize,
    graph: Vec<Vec<Edge>>,
}

impl MaxFlow {
    pub fn new(n: usize) -> Self {
        MaxFlow {
            n,
            graph: vec![Vec::new(); n],
        }
    }
    
    /// 添加边
    pub fn add_edge(&mut self, from: usize, to: usize, capacity: i64) {
        let from_len = self.graph[from].len();
        let to_len = self.graph[to].len();
        
        // 正向边
        self.graph[from].push(Edge {
            to,
            rev: to_len,
            capacity,
            flow: 0,
        });
        
        // 反向边（初始容量为0）
        self.graph[to].push(Edge {
            to: from,
            rev: from_len,
            capacity: 0,
            flow: 0,
        });
    }
    
    /// Ford-Fulkerson算法 (DFS)
    /// 
    /// # 复杂度
    /// - 时间: O(E * |f*|) 其中|f*|是最大流值
    /// - 适用于小容量网络
    pub fn ford_fulkerson(&mut self, source: usize, sink: usize) -> i64 {
        let mut max_flow = 0;
        
        loop {
            let mut visited = vec![false; self.n];
            let flow = self.dfs(source, sink, i64::MAX, &mut visited);
            
            if flow == 0 {
                break;
            }
            
            max_flow += flow;
        }
        
        max_flow
    }
    
    fn dfs(&mut self, u: usize, sink: usize, min_cap: i64, visited: &mut [bool]) -> i64 {
        if u == sink {
            return min_cap;
        }
        
        visited[u] = true;
        
        for i in 0..self.graph[u].len() {
            let edge = &self.graph[u][i];
            let remaining = edge.capacity - edge.flow;
            
            if !visited[edge.to] && remaining > 0 {
                let flow = self.dfs(edge.to, sink, min(min_cap, remaining), visited);
                
                if flow > 0 {
                    // 更新正向边
                    self.graph[u][i].flow += flow;
                    // 更新反向边
                    let rev_idx = self.graph[u][i].rev;
                    self.graph[edge.to][rev_idx].flow -= flow;
                    return flow;
                }
            }
        }
        
        0
    }
    
    /// Edmonds-Karp算法 (BFS找最短增广路)
    /// 
    /// # 复杂度
    /// - 时间: O(V * E^2)
    /// - 多项式时间保证
    pub fn edmonds_karp(&mut self, source: usize, sink: usize) -> i64 {
        let mut max_flow = 0;
        
        loop {
            let (flow, parent) = self.bfs(source, sink);
            
            if flow == 0 {
                break;
            }
            
            // 更新路径上的流
            let mut v = sink;
            while v != source {
                let (u, edge_idx) = parent[v];
                
                // 更新正向边
                self.graph[u][edge_idx].flow += flow;
                
                // 更新反向边
                let edge = &self.graph[u][edge_idx];
                let rev_idx = edge.rev;
                self.graph[v][rev_idx].flow -= flow;
                
                v = u;
            }
            
            max_flow += flow;
        }
        
        max_flow
    }
    
    fn bfs(&self, source: usize, sink: usize) -> (i64, Vec<(usize, usize)>) {
        let mut parent = vec![(0, 0); self.n];  // (父节点, 边索引)
        let mut visited = vec![false; self.n];
        let mut queue = VecDeque::new();
        
        visited[source] = true;
        queue.push_back(source);
        
        while let Some(u) = queue.pop_front() {
            for (i, edge) in self.graph[u].iter().enumerate() {
                let remaining = edge.capacity - edge.flow;
                
                if !visited[edge.to] && remaining > 0 {
                    visited[edge.to] = true;
                    parent[edge.to] = (u, i);
                    
                    if edge.to == sink {
                        // 找到路径，计算瓶颈容量
                        let mut flow = i64::MAX;
                        let mut v = sink;
                        while v != source {
                            let (u, edge_idx) = parent[v];
                            let remaining = self.graph[u][edge_idx].capacity - self.graph[u][edge_idx].flow;
                            flow = min(flow, remaining);
                            v = u;
                        }
                        return (flow, parent);
                    }
                    
                    queue.push_back(edge.to);
                }
            }
        }
        
        (0, parent)
    }
    
    /// Dinic算法
    /// 
    /// # 复杂度
    /// - 时间: O(E * V^2) 一般情况，O(E * sqrt(V)) 单位网络
    /// - 实际性能优秀
    pub fn dinic(&mut self, source: usize, sink: usize) -> i64 {
        let mut max_flow = 0;
        
        loop {
            // 构建层次图
            let level = self.build_level_graph(source);
            
            if level[sink] < 0 {
                break;  // 无法到达汇点
            }
            
            let mut ptr = vec![0; self.n];  // 当前弧优化
            
            loop {
                let flow = self.dinic_dfs(source, sink, i64::MAX, &level, &mut ptr);
                if flow == 0 {
                    break;
                }
                max_flow += flow;
            }
        }
        
        max_flow
    }
    
    fn build_level_graph(&self, source: usize) -> Vec<i32> {
        let mut level = vec![-1; self.n];
        let mut queue = VecDeque::new();
        
        level[source] = 0;
        queue.push_back(source);
        
        while let Some(u) = queue.pop_front() {
            for edge in &self.graph[u] {
                let remaining = edge.capacity - edge.flow;
                
                if level[edge.to] < 0 && remaining > 0 {
                    level[edge.to] = level[u] + 1;
                    queue.push_back(edge.to);
                }
            }
        }
        
        level
    }
    
    fn dinic_dfs(&mut self, u: usize, sink: usize, min_cap: i64, 
                 level: &[i32], ptr: &mut [usize]) -> i64 {
        if u == sink {
            return min_cap;
        }
        
        while ptr[u] < self.graph[u].len() {
            let i = ptr[u];
            let edge = &self.graph[u][i];
            
            let remaining = edge.capacity - edge.flow;
            
            if remaining > 0 && level[edge.to] == level[u] + 1 {
                let flow = self.dinic_dfs(edge.to, sink, min(min_cap, remaining), level, ptr);
                
                if flow > 0 {
                    // 更新正向边
                    self.graph[u][i].flow += flow;
                    // 更新反向边
                    let rev_idx = self.graph[u][i].rev;
                    self.graph[edge.to][rev_idx].flow -= flow;
                    return flow;
                }
            }
            
            ptr[u] += 1;
        }
        
        0
    }
    
    /// 获取当前流
    pub fn get_flow(&self, from: usize, edge_idx: usize) -> i64 {
        self.graph[from][edge_idx].flow
    }
    
    /// 获取残量网络中的边
    pub fn get_edges(&self) -> &Vec<Vec<Edge>> {
        &self.graph
    }
}

/// 最小割 (通过最大流-最小割定理)
pub fn min_cut(max_flow: &MaxFlow, source: usize) -> Vec<usize> {
    // 在残量网络中从源点可达的顶点构成S集
    let n = max_flow.get_edges().len();
    let mut visited = vec![false; n];
    let mut queue = VecDeque::new();
    
    visited[source] = true;
    queue.push_back(source);
    
    while let Some(u) = queue.pop_front() {
        for edge in &max_flow.get_edges()[u] {
            let remaining = edge.capacity - edge.flow;
            if remaining > 0 && !visited[edge.to] {
                visited[edge.to] = true;
                queue.push_back(edge.to);
            }
        }
    }
    
    visited.iter().enumerate()
        .filter(|(_, &v)| v)
        .map(|(i, _)| i)
        .collect()
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_max_flow_basic() {
        // CLRS Figure 26.1 示例
        let mut mf = MaxFlow::new(6);
        
        // 边: from -> (to, capacity)
        mf.add_edge(0, 1, 16);  // s->v1
        mf.add_edge(0, 2, 13);  // s->v2
        mf.add_edge(1, 2, 10);  // v1->v2
        mf.add_edge(1, 3, 12);  // v1->v3
        mf.add_edge(2, 1, 4);   // v2->v1
        mf.add_edge(2, 4, 14);  // v2->v4
        mf.add_edge(3, 2, 9);   // v3->v2
        mf.add_edge(3, 5, 20);  // v3->t
        mf.add_edge(4, 3, 7);   // v4->v3
        mf.add_edge(4, 5, 4);   // v4->t
        
        let flow = mf.edmonds_karp(0, 5);
        assert_eq!(flow, 23);
    }
    
    #[test]
    fn test_dinic() {
        let mut mf = MaxFlow::new(6);
        
        mf.add_edge(0, 1, 16);
        mf.add_edge(0, 2, 13);
        mf.add_edge(1, 2, 10);
        mf.add_edge(1, 3, 12);
        mf.add_edge(2, 1, 4);
        mf.add_edge(2, 4, 14);
        mf.add_edge(3, 2, 9);
        mf.add_edge(3, 5, 20);
        mf.add_edge(4, 3, 7);
        mf.add_edge(4, 5, 4);
        
        let flow = mf.dinic(0, 5);
        assert_eq!(flow, 23);
    }
    
    #[test]
    fn test_simple_flow() {
        // 简单网络: s -> a -> t
        let mut mf = MaxFlow::new(3);
        mf.add_edge(0, 1, 10);
        mf.add_edge(1, 2, 5);
        
        let flow = mf.edmonds_karp(0, 2);
        assert_eq!(flow, 5);  // 受限于第二条边
    }
}
