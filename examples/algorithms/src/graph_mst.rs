//! 最小生成树算法
//! 
//! 包含:
//! - Kruskal算法: O(E log E)
//! - Prim算法: O(E log V)
//! 
//! 对标: MIT 6.046 / CLRS Chapter 23

use std::collections::BinaryHeap;
use std::cmp::Ordering;

/// 带权边
#[derive(Clone, Copy, Debug)]
pub struct Edge {
    pub u: usize,
    pub v: usize,
    pub weight: i32,
}

impl Edge {
    pub fn new(u: usize, v: usize, weight: i32) -> Self {
        Edge { u, v, weight }
    }
}

/// 并查集 (Union-Find) 用于Kruskal算法
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
}

impl UnionFind {
    pub fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
        }
    }
    
    /// 带路径压缩的查找
    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    /// 按秩合并
    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let px = self.find(x);
        let py = self.find(y);
        
        if px == py {
            return false;  // 已在同一集合
        }
        
        // 按秩合并
        if self.rank[px] < self.rank[py] {
            self.parent[px] = py;
        } else if self.rank[px] > self.rank[py] {
            self.parent[py] = px;
        } else {
            self.parent[py] = px;
            self.rank[px] += 1;
        }
        true
    }
}

/// Kruskal算法
/// 
/// # 复杂度
/// - 时间: O(E log E) = O(E log V) (排序主导)
/// - 空间: O(V) (并查集)
/// 
/// # 正确性
/// 基于切分性质: 对于任意切分，最小横切边必在MST中
pub fn kruskal(n: usize, mut edges: Vec<Edge>) -> (Vec<Edge>, i32) {
    // 按权重排序
    edges.sort_by_key(|e| e.weight);
    
    let mut uf = UnionFind::new(n);
    let mut mst = Vec::new();
    let mut total_weight = 0;
    
    for edge in edges {
        if uf.union(edge.u, edge.v) {
            mst.push(edge);
            total_weight += edge.weight;
            
            if mst.len() == n - 1 {
                break;  // MST有n-1条边
            }
        }
    }
    
    (mst, total_weight)
}

/// Prim算法的优先队列节点
#[derive(Clone, Copy)]
struct PrimNode {
    vertex: usize,
    key: i32,
}

impl Ord for PrimNode {
    fn cmp(&self, other: &Self) -> Ordering {
        other.key.cmp(&self.key)  // 最小堆
    }
}

impl PartialOrd for PrimNode {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(self.cmp(other))
    }
}

impl PartialEq for PrimNode {
    fn eq(&self, other: &Self) -> bool {
        self.key == other.key
    }
}

impl Eq for PrimNode {}

/// Prim算法 (使用邻接矩阵)
/// 
/// # 复杂度
/// - 时间: O(V²) - 简单实现
/// - 时间: O(E log V) - 二叉堆优化
/// - 空间: O(V)
pub fn prim(graph: &[Vec<i32>]) -> (Vec<(usize, usize)>, i32) {
    let n = graph.len();
    let mut key = vec![i32::MAX; n];  // 到MST的最小距离
    let mut parent = vec![None; n];   // MST中的父节点
    let mut in_mst = vec![false; n];
    
    let mut heap = BinaryHeap::new();
    
    // 从顶点0开始
    key[0] = 0;
    heap.push(PrimNode { vertex: 0, key: 0 });
    
    while let Some(node) = heap.pop() {
        let u = node.vertex;
        
        if in_mst[u] {
            continue;
        }
        
        in_mst[u] = true;
        
        // 更新邻接顶点
        for v in 0..n {
            if graph[u][v] > 0 && !in_mst[v] && graph[u][v] < key[v] {
                key[v] = graph[u][v];
                parent[v] = Some(u);
                heap.push(PrimNode { vertex: v, key: key[v] });
            }
        }
    }
    
    // 构建结果
    let mut mst_edges = Vec::new();
    let mut total_weight = 0;
    
    for v in 1..n {
        if let Some(u) = parent[v] {
            mst_edges.push((u, v));
            total_weight += graph[u][v];
        }
    }
    
    (mst_edges, total_weight)
}

/// Prim算法 (使用邻接表)
pub fn prim_adj_list(adj: &[Vec<(usize, i32)>]) -> i32 {
    let n = adj.len();
    let mut key = vec![i32::MAX; n];
    let mut in_mst = vec![false; n];
    let mut heap = BinaryHeap::new();
    
    key[0] = 0;
    heap.push(PrimNode { vertex: 0, key: 0 });
    
    let mut total_weight = 0;
    
    while let Some(node) = heap.pop() {
        let u = node.vertex;
        
        if in_mst[u] {
            continue;
        }
        
        in_mst[u] = true;
        total_weight += node.key;
        
        for &(v, weight) in &adj[u] {
            if !in_mst[v] && weight < key[v] {
                key[v] = weight;
                heap.push(PrimNode { vertex: v, key: weight });
            }
        }
    }
    
    total_weight
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_kruskal() {
        // 测试图: CLRS Figure 23.1
        let edges = vec![
            Edge::new(0, 1, 4),
            Edge::new(0, 7, 8),
            Edge::new(1, 2, 8),
            Edge::new(1, 7, 11),
            Edge::new(2, 3, 7),
            Edge::new(2, 5, 4),
            Edge::new(2, 8, 2),
            Edge::new(3, 4, 9),
            Edge::new(3, 5, 14),
            Edge::new(4, 5, 10),
            Edge::new(5, 6, 2),
            Edge::new(6, 7, 1),
            Edge::new(6, 8, 6),
            Edge::new(7, 8, 7),
        ];
        
        let (mst, weight) = kruskal(9, edges);
        
        assert_eq!(mst.len(), 8);  // 9个顶点，MST有8条边
        assert_eq!(weight, 37);     // CLRS中的最优值
    }
    
    #[test]
    fn test_prim() {
        // 使用邻接矩阵
        let inf = i32::MAX / 2;
        let graph = vec![
            vec![0, 4, inf, inf, inf, inf, inf, 8, inf],
            vec![4, 0, 8, inf, inf, inf, inf, 11, inf],
            vec![inf, 8, 0, 7, inf, 4, inf, inf, 2],
            vec![inf, inf, 7, 0, 9, 14, inf, inf, inf],
            vec![inf, inf, inf, 9, 0, 10, inf, inf, inf],
            vec![inf, inf, 4, 14, 10, 0, 2, inf, inf],
            vec![inf, inf, inf, inf, inf, 2, 0, 1, 6],
            vec![8, 11, inf, inf, inf, inf, 1, 0, 7],
            vec![inf, inf, 2, inf, inf, inf, 6, 7, 0],
        ];
        
        let (mst, weight) = prim(&graph);
        
        assert_eq!(mst.len(), 8);
        assert_eq!(weight, 37);
    }
    
    #[test]
    fn test_union_find() {
        let mut uf = UnionFind::new(5);
        
        assert!(uf.union(0, 1));
        assert!(uf.union(2, 3));
        assert!(uf.union(1, 2));
        
        // 0,1,2,3在同一集合
        assert_eq!(uf.find(0), uf.find(3));
        
        // 4在另一集合
        assert_ne!(uf.find(0), uf.find(4));
        
        // 重复合并应返回false
        assert!(!uf.union(0, 2));
    }
}
