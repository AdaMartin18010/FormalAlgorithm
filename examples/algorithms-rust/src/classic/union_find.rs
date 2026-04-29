//! 并查集 (Union-Find) 实现
//! 
//! 支持:
//! - 路径压缩
//! - 按秩合并
//! 
//! 复杂度: 几乎 O(1)

/// 并查集
pub struct UnionFind {
    parent: Vec<usize>,
    rank: Vec<usize>,
    count: usize,  // 连通分量数
}

impl UnionFind {
    /// 创建n个元素的并查集
    pub fn new(n: usize) -> Self {
        UnionFind {
            parent: (0..n).collect(),
            rank: vec![0; n],
            count: n,
        }
    }
    
    /// 查找根节点 (路径压缩)
    pub fn find(&mut self, x: usize) -> usize {
        if self.parent[x] != x {
            self.parent[x] = self.find(self.parent[x]);
        }
        self.parent[x]
    }
    
    /// 合并两个集合 (按秩合并)
    /// 
    /// 返回: 是否实际发生了合并
    pub fn union(&mut self, x: usize, y: usize) -> bool {
        let px = self.find(x);
        let py = self.find(y);
        
        if px == py {
            return false;
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
        
        self.count -= 1;
        true
    }
    
    /// 检查两个元素是否在同一集合
    pub fn connected(&mut self, x: usize, y: usize) -> bool {
        self.find(x) == self.find(y)
    }
    
    /// 获取连通分量数
    pub fn count(&self) -> usize {
        self.count
    }
    
    /// 获取某集合的大小
    pub fn set_size(&mut self, x: usize) -> usize {
        let root = self.find(x);
        let n = self.parent.len();
        let mut count = 0;
        for i in 0..n {
            if self.find(i) == root {
                count += 1;
            }
        }
        count
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_basic() {
        let mut uf = UnionFind::new(5);
        
        assert_eq!(uf.count(), 5);
        
        uf.union(0, 1);
        uf.union(1, 2);
        
        assert!(uf.connected(0, 2));
        assert!(!uf.connected(0, 3));
        assert_eq!(uf.count(), 3);
    }
    
    #[test]
    fn test_path_compression() {
        let mut uf = UnionFind::new(5);
        
        // 创建链式结构
        uf.union(0, 1);
        uf.union(1, 2);
        uf.union(2, 3);
        uf.union(3, 4);
        
        // 查找应该压缩路径
        let root = uf.find(4);
        assert!(uf.connected(0, 4));
        
        // 验证所有节点都指向根
        for i in 0..5 {
            assert_eq!(uf.find(i), root);
        }
    }
}
