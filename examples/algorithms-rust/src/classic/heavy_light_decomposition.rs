//! 树链剖分 (Heavy-Light Decomposition, HLD)
//!
//! 一种将树分解为若干条不相交重链的数据结构，支持高效的路径查询与修改。
//!
//! ## 核心思想
//! - 将树中的边分为重边和轻边
//! - 重边连接父节点和其重儿子（子树最大的儿子）
//! - 多条重边形成一条重链，轻边连接不同重链
//! - 利用线段树或树状数组维护重链，将路径查询转化为 O(log²n) 的链上操作
//!
//! ## 适用问题
//! - 树上路径权值和/最大/最小值查询
//! - 树上路径权值修改
//! - 子树权值查询与修改
//! - LCA（最近公共祖先）查询
//!
//! ## 复杂度分析
//! - 预处理: O(n)
//! - 路径查询/修改: O(log²n)
//! - 子树查询/修改: O(log n)
//! - 空间: O(n)
//!
//! 对标: 竞赛编程标准数据结构

use super::segment_tree::SegmentTree;

/// 树链剖分结构
pub struct HeavyLightDecomposition {
    /// 树的邻接表（存目标节点和边权）
    adj: Vec<Vec<(usize, i64)>>,
    /// 父节点
    parent: Vec<usize>,
    /// 深度
    depth: Vec<usize>,
    /// 重儿子
    heavy_child: Vec<Option<usize>>,
    /// 子树大小
    subtree_size: Vec<usize>,
    /// 所在重链的顶端节点
    chain_top: Vec<usize>,
    /// 节点在 DFS 序中的位置
    dfn: Vec<usize>,
    /// DFS 序对应的节点（逆映射）
    dfn_to_node: Vec<usize>,
    /// 当前 DFS 时间戳
    current_dfn: usize,
    /// 节点权值（按 DFS 序排列，用于线段树）
    values: Vec<i64>,
    /// 节点数量
    n: usize,
}

impl HeavyLightDecomposition {
    /// 创建树链剖分结构
    ///
    /// # 参数
    /// - `n`: 节点数量（节点编号 0..n-1）
    /// - `values`: 每个节点的初始权值
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn new(n: usize, values: Vec<i64>) -> Self {
        HeavyLightDecomposition {
            adj: vec![vec![]; n],
            parent: vec![0; n],
            depth: vec![0; n],
            heavy_child: vec![None; n],
            subtree_size: vec![0; n],
            chain_top: vec![0; n],
            dfn: vec![0; n],
            dfn_to_node: vec![0; n],
            current_dfn: 0,
            values,
            n,
        }
    }

    /// 添加边（无向树）
    ///
    /// # 参数
    /// - `u`, `v`: 边的两个端点
    /// - `w`: 边权
    pub fn add_edge(&mut self, u: usize, v: usize, w: i64) {
        self.adj[u].push((v, w));
        self.adj[v].push((u, w));
    }

    /// 第一次 DFS：计算子树大小、父节点、深度、重儿子
    fn dfs1(&mut self, u: usize, p: usize) {
        self.parent[u] = p;
        self.subtree_size[u] = 1;

        let mut max_size = 0;
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v == p {
                continue;
            }
            self.depth[v] = self.depth[u] + 1;
            self.dfs1(v, u);
            self.subtree_size[u] += self.subtree_size[v];
            if self.subtree_size[v] > max_size {
                max_size = self.subtree_size[v];
                self.heavy_child[u] = Some(v);
            }
        }
    }

    /// 第二次 DFS：分配 DFS 序、确定链顶
    fn dfs2(&mut self, u: usize, top: usize) {
        self.chain_top[u] = top;
        self.dfn[u] = self.current_dfn;
        self.dfn_to_node[self.current_dfn] = u;
        self.current_dfn += 1;

        // 先访问重儿子（保证重链连续）
        if let Some(hc) = self.heavy_child[u] {
            self.dfs2(hc, top);
        }

        // 再访问轻儿子
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v != self.parent[u] && Some(v) != self.heavy_child[u] {
                self.dfs2(v, v);
            }
        }
    }

    /// 预处理树链剖分
    ///
    /// # 参数
    /// - `root`: 根节点
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn decompose(&mut self, root: usize) {
        self.depth[root] = 0;
        self.dfs1(root, root);
        self.dfs2(root, root);
    }

    /// 查询从 u 到 v 路径上的权值和
    ///
    /// # 参数
    /// - `seg_tree`: 线段树
    /// - `u`, `v`: 路径的两个端点
    ///
    /// # 返回值
    /// 路径上所有节点的权值和
    ///
    /// # 复杂度
    /// - 时间: O(log²n)
    pub fn query_path_sum(&self, seg_tree: &SegmentTree<i64>, u: usize, v: usize) -> i64 {
        let mut res = 0i64;
        let (mut u, mut v) = (u, v);

        while self.chain_top[u] != self.chain_top[v] {
            if self.depth[self.chain_top[u]] < self.depth[self.chain_top[v]] {
                std::mem::swap(&mut u, &mut v);
            }
            // u 所在链的顶端深度更大，先处理 u 的链
            let top = self.chain_top[u];
            res += seg_tree.query(self.dfn[top], self.dfn[u]);
            u = self.parent[top];
        }

        // 现在 u 和 v 在同一条链上
        if self.depth[u] > self.depth[v] {
            std::mem::swap(&mut u, &mut v);
        }
        res += seg_tree.query(self.dfn[u], self.dfn[v]);
        res
    }

    /// 查询从 u 到 v 路径上的权值最大值
    ///
    /// # 复杂度
    /// - 时间: O(log²n)
    pub fn query_path_max(&self, seg_tree: &SegmentTree<i64>, u: usize, v: usize) -> i64 {
        let mut res = i64::MIN;
        let (mut u, mut v) = (u, v);

        while self.chain_top[u] != self.chain_top[v] {
            if self.depth[self.chain_top[u]] < self.depth[self.chain_top[v]] {
                std::mem::swap(&mut u, &mut v);
            }
            let top = self.chain_top[u];
            let chain_max = seg_tree.query(self.dfn[top], self.dfn[u]);
            res = res.max(chain_max);
            u = self.parent[top];
        }

        if self.depth[u] > self.depth[v] {
            std::mem::swap(&mut u, &mut v);
        }
        let final_max = seg_tree.query(self.dfn[u], self.dfn[v]);
        res.max(final_max)
    }

    /// 修改路径上的节点权值
    ///
    /// # 参数
    /// - `seg_tree`: 线段树的可变引用
    /// - `u`, `v`: 路径的两个端点
    /// - `new_val`: 新权值
    ///
    /// # 复杂度
    /// - 时间: O(log²n)
    pub fn update_path(&self, seg_tree: &mut SegmentTree<i64>, u: usize, v: usize, new_val: i64) {
        let (mut u, mut v) = (u, v);

        while self.chain_top[u] != self.chain_top[v] {
            if self.depth[self.chain_top[u]] < self.depth[self.chain_top[v]] {
                std::mem::swap(&mut u, &mut v);
            }
            let top = self.chain_top[u];
            for dfn in self.dfn[top]..=self.dfn[u] {
                seg_tree.update(dfn, new_val);
            }
            u = self.parent[top];
        }

        if self.depth[u] > self.depth[v] {
            std::mem::swap(&mut u, &mut v);
        }
        for dfn in self.dfn[u]..=self.dfn[v] {
            seg_tree.update(dfn, new_val);
        }
    }

    /// 查询以 u 为根的子树的权值和
    ///
    /// # 复杂度
    /// - 时间: O(log n)
    pub fn query_subtree_sum(&self, seg_tree: &SegmentTree<i64>, u: usize) -> i64 {
        seg_tree.query(self.dfn[u], self.dfn[u] + self.subtree_size[u] - 1)
    }

    /// 修改节点 u 的权值
    ///
    /// # 复杂度
    /// - 时间: O(log n)
    pub fn update_node(&self, seg_tree: &mut SegmentTree<i64>, u: usize, new_val: i64) {
        seg_tree.update(self.dfn[u], new_val);
    }

    /// 查询 LCA（最近公共祖先）
    ///
    /// # 复杂度
    /// - 时间: O(log n)
    pub fn lca(&self, mut u: usize, mut v: usize) -> usize {
        while self.chain_top[u] != self.chain_top[v] {
            if self.depth[self.chain_top[u]] < self.depth[self.chain_top[v]] {
                std::mem::swap(&mut u, &mut v);
            }
            u = self.parent[self.chain_top[u]];
        }
        if self.depth[u] < self.depth[v] { u } else { v }
    }

    /// 计算两点间距离（边权之和）
    ///
    /// # 复杂度
    /// - 时间: O(log²n)
    pub fn distance(&self, u: usize, v: usize) -> usize {
        self.depth[u] + self.depth[v] - 2 * self.depth[self.lca(u, v)]
    }

    /// 获取 DFS 序中的值数组（用于构建线段树）
    pub fn get_dfn_values(&self) -> Vec<i64> {
        let mut res = vec![0i64; self.n];
        for i in 0..self.n {
            res[self.dfn[i]] = self.values[i];
        }
        res
    }

    /// 获取节点 u 的 DFS 序
    pub fn get_dfn(&self, u: usize) -> usize {
        self.dfn[u]
    }

    /// 获取 DFS 序对应的节点
    pub fn get_node_at_dfn(&self, dfn: usize) -> usize {
        self.dfn_to_node[dfn]
    }
}

/// 简化版 HLD，封装线段树操作
pub struct HeavyLightDecompositionWithSegTree {
    hld: HeavyLightDecomposition,
    seg_tree_sum: SegmentTree<i64>,
    seg_tree_max: SegmentTree<i64>,
}

impl HeavyLightDecompositionWithSegTree {
    /// 创建带线段树的 HLD
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn new(n: usize, values: Vec<i64>) -> Self {
        let hld = HeavyLightDecomposition::new(n, values.clone());
        // 临时空数组，等 decompose 后再创建线段树
        let dummy = vec![0i64; n];
        let seg_tree_sum = SegmentTree::new(&dummy, 0, |a, b| a + b);
        let seg_tree_max = SegmentTree::new(&dummy, i64::MIN, |a, b| a.max(b));

        HeavyLightDecompositionWithSegTree {
            hld,
            seg_tree_sum,
            seg_tree_max,
        }
    }

    /// 添加边
    pub fn add_edge(&mut self, u: usize, v: usize, w: i64) {
        self.hld.add_edge(u, v, w);
    }

    /// 预处理
    pub fn decompose(&mut self, root: usize) {
        self.hld.decompose(root);
        let dfn_values = self.hld.get_dfn_values();
        self.seg_tree_sum = SegmentTree::new(&dfn_values, 0, |a, b| a + b);
        self.seg_tree_max = SegmentTree::new(&dfn_values, i64::MIN, |a, b| a.max(b));
    }

    /// 查询路径和
    pub fn query_path_sum(&self, u: usize, v: usize) -> i64 {
        self.hld.query_path_sum(&self.seg_tree_sum, u, v)
    }

    /// 查询路径最大值
    pub fn query_path_max(&self, u: usize, v: usize) -> i64 {
        self.hld.query_path_max(&self.seg_tree_max, u, v)
    }

    /// 修改节点值
    pub fn update_node(&mut self, u: usize, new_val: i64) {
        self.hld.update_node(&mut self.seg_tree_sum, u, new_val);
        self.hld.update_node(&mut self.seg_tree_max, u, new_val);
    }

    /// 查询子树和
    pub fn query_subtree_sum(&self, u: usize) -> i64 {
        self.hld.query_subtree_sum(&self.seg_tree_sum, u)
    }

    /// 查询 LCA
    pub fn lca(&self, u: usize, v: usize) -> usize {
        self.hld.lca(u, v)
    }

    /// 计算距离
    pub fn distance(&self, u: usize, v: usize) -> usize {
        self.hld.distance(u, v)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_hld() {
        // 树结构:
        //       0(5)
        //      /   \
        //    1(3)  2(7)
        //   /   \
        // 3(2)  4(4)
        let n = 5;
        let values = vec![5, 3, 7, 2, 4];
        let mut hld = HeavyLightDecompositionWithSegTree::new(n, values);

        hld.add_edge(0, 1, 1);
        hld.add_edge(0, 2, 1);
        hld.add_edge(1, 3, 1);
        hld.add_edge(1, 4, 1);

        hld.decompose(0);

        // 测试路径和
        assert_eq!(hld.query_path_sum(3, 4), 2 + 3 + 4); // 3->1->4
        assert_eq!(hld.query_path_sum(0, 4), 5 + 3 + 4); // 0->1->4
        assert_eq!(hld.query_path_sum(2, 3), 7 + 5 + 3 + 2); // 2->0->1->3

        // 测试路径最大值
        assert_eq!(hld.query_path_max(3, 4), 4);
        assert_eq!(hld.query_path_max(0, 4), 5);

        // 测试子树和
        assert_eq!(hld.query_subtree_sum(1), 3 + 2 + 4); // 节点1及其子树
        assert_eq!(hld.query_subtree_sum(0), 5 + 3 + 7 + 2 + 4); // 整棵树

        // 测试 LCA
        assert_eq!(hld.lca(3, 4), 1);
        assert_eq!(hld.lca(2, 3), 0);
        assert_eq!(hld.lca(1, 4), 1);

        // 测试距离
        assert_eq!(hld.distance(3, 4), 2); // 3->1->4
        assert_eq!(hld.distance(2, 3), 3); // 2->0->1->3
    }

    #[test]
    fn test_chain_tree() {
        // 链状树: 0-1-2-3-4
        let n = 5;
        let values = vec![1, 2, 3, 4, 5];
        let mut hld = HeavyLightDecompositionWithSegTree::new(n, values);

        for i in 0..n - 1 {
            hld.add_edge(i, i + 1, 1);
        }

        hld.decompose(0);

        // 路径和
        assert_eq!(hld.query_path_sum(0, 4), 15);
        assert_eq!(hld.query_path_sum(1, 3), 9);

        // 路径最大值
        assert_eq!(hld.query_path_max(0, 4), 5);
        assert_eq!(hld.query_path_max(0, 2), 3);
    }

    #[test]
    fn test_star_tree() {
        // 星形树：根节点0连接所有其他节点
        let n = 6;
        let values = vec![10, 1, 2, 3, 4, 5];
        let mut hld = HeavyLightDecompositionWithSegTree::new(n, values);

        for i in 1..n {
            hld.add_edge(0, i, 1);
        }

        hld.decompose(0);

        // 路径和（都经过根节点）
        assert_eq!(hld.query_path_sum(1, 2), 1 + 10 + 2);
        assert_eq!(hld.query_path_sum(3, 5), 3 + 10 + 5);

        // LCA 都是根节点
        assert_eq!(hld.lca(1, 5), 0);
        assert_eq!(hld.lca(2, 3), 0);
    }

    #[test]
    fn test_update() {
        let n = 4;
        let values = vec![1, 2, 3, 4];
        let mut hld = HeavyLightDecompositionWithSegTree::new(n, values);

        hld.add_edge(0, 1, 1);
        hld.add_edge(0, 2, 1);
        hld.add_edge(2, 3, 1);

        hld.decompose(0);

        // 更新前
        assert_eq!(hld.query_path_sum(0, 3), 1 + 3 + 4);

        // 更新节点2
        hld.update_node(2, 10);

        // 更新后
        assert_eq!(hld.query_path_sum(0, 3), 1 + 10 + 4);
        assert_eq!(hld.query_subtree_sum(2), 10 + 4);
    }

    #[test]
    fn test_single_node() {
        let n = 1;
        let values = vec![42];
        let mut hld = HeavyLightDecompositionWithSegTree::new(n, values);
        hld.decompose(0);

        assert_eq!(hld.query_path_sum(0, 0), 42);
        assert_eq!(hld.query_path_max(0, 0), 42);
        assert_eq!(hld.lca(0, 0), 0);
    }
}
