//! 树上并查集 (DSU on Tree / Small-to-Large Merging)
//!
//! 一种用于解决子树统计问题的高效算法，通过"小合并到大"的策略优化复杂度。
//!
//! ## 核心思想
//! - 对于每个节点，保留其重儿子（子树最大的儿子）的统计信息
//! - 轻儿子的统计信息计算后丢弃
//! - 利用重儿子的结果，暴力合并轻儿子的信息
//!
//! ## 适用问题
//! - 子树中每种颜色出现次数
//! - 子树中不同颜色数量
//! - 子树中满足某种条件的节点数
//!
//! ## 复杂度分析
//! - 时间: O(n log n)，每个节点最多被合并 O(log n) 次
//! - 空间: O(n)
//!
//! 对标: Codeforces/AtCoder 竞赛算法

use std::collections::HashMap;

/// 树上并查集结构
pub struct DsuOnTree {
    /// 树的邻接表表示
    adj: Vec<Vec<usize>>,
    /// 节点颜色/值
    colors: Vec<usize>,
    /// 子树大小
    subtree_size: Vec<usize>,
    /// 重儿子
    heavy_child: Vec<Option<usize>>,
    /// 是否保留当前子树的标记
    keep: Vec<bool>,
    /// 当前统计的颜色频率
    freq: HashMap<usize, usize>,
    /// 当前不同颜色的数量
    distinct_count: usize,
    /// 每个节点的答案
    ans: Vec<usize>,
}

impl DsuOnTree {
    /// 创建树上并查集
    ///
    /// # 参数
    /// - `n`: 节点数量（节点编号 0..n-1）
    /// - `colors`: 每个节点的颜色数组
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn new(n: usize, colors: Vec<usize>) -> Self {
        DsuOnTree {
            adj: vec![vec![]; n],
            colors,
            subtree_size: vec![0; n],
            heavy_child: vec![None; n],
            keep: vec![false; n],
            freq: HashMap::new(),
            distinct_count: 0,
            ans: vec![0; n],
        }
    }

    /// 添加边（无向树）
    pub fn add_edge(&mut self, u: usize, v: usize) {
        self.adj[u].push(v);
        self.adj[v].push(u);
    }

    /// 计算子树大小和重儿子
    fn dfs_size(&mut self, u: usize, parent: usize) {
        self.subtree_size[u] = 1;
        let mut max_size = 0;

        for i in 0..self.adj[u].len() {
            let v = self.adj[u][i];
            if v == parent {
                continue;
            }
            self.dfs_size(v, u);
            self.subtree_size[u] += self.subtree_size[v];
            if self.subtree_size[v] > max_size {
                max_size = self.subtree_size[v];
                self.heavy_child[u] = Some(v);
            }
        }
    }

    /// 添加节点 u 的子树信息到全局统计
    fn add_subtree(&mut self, u: usize, parent: usize) {
        // 添加当前节点
        self.add_node(u);

        // 递归添加所有子节点
        for i in 0..self.adj[u].len() {
            let v = self.adj[u][i];
            if v != parent && !self.keep[v] {
                self.add_subtree(v, u);
            }
        }
    }

    /// 添加单个节点的信息
    fn add_node(&mut self, u: usize) {
        let color = self.colors[u];
        let count = self.freq.entry(color).or_insert(0);
        if *count == 0 {
            self.distinct_count += 1;
        }
        *count += 1;
    }

    /// 主 DFS 过程
    fn dfs(&mut self, u: usize, parent: usize, keep_flag: bool) {
        // 先处理所有轻儿子
        for i in 0..self.adj[u].len() {
            let v = self.adj[u][i];
            if v != parent && self.heavy_child[u] != Some(v) {
                self.dfs(v, u, false);
            }
        }

        // 处理重儿子（保留其信息）
        if let Some(hc) = self.heavy_child[u] {
            self.dfs(hc, u, true);
            self.keep[hc] = true;
        }

        // 再次添加所有轻儿子的信息
        for i in 0..self.adj[u].len() {
            let v = self.adj[u][i];
            if v != parent && self.heavy_child[u] != Some(v) {
                self.add_subtree(v, u);
            }
        }

        // 添加当前节点
        self.add_node(u);

        // 计算当前节点的答案
        self.ans[u] = self.distinct_count;

        // 取消重儿子的保留标记
        if let Some(hc) = self.heavy_child[u] {
            self.keep[hc] = false;
        }

        // 如果不保留，清除当前子树的信息
        if !keep_flag {
            self.clear_subtree(u, parent);
        }
    }

    /// 清除子树信息
    fn clear_subtree(&mut self, u: usize, parent: usize) {
        let color = self.colors[u];
        if let Some(count) = self.freq.get_mut(&color) {
            *count -= 1;
            if *count == 0 {
                self.distinct_count -= 1;
            }
        }

        for i in 0..self.adj[u].len() {
            let v = self.adj[u][i];
            if v != parent && !self.keep[v] {
                self.clear_subtree(v, u);
            }
        }
    }

    /// 运行 DSU on Tree 算法
    ///
    /// # 返回值
    /// 返回每个节点为根的子树中不同颜色的数量
    ///
    /// # 复杂度
    /// - 时间: O(n log n)
    /// - 空间: O(n)
    pub fn solve(mut self, root: usize) -> Vec<usize> {
        self.dfs_size(root, root);
        self.dfs(root, root, true);
        self.ans
    }

    /// 获取某个子树的颜色频率表（调试用）
    pub fn get_freq(&self) -> &HashMap<usize, usize> {
        &self.freq
    }
}

/// 简化版 DSU on Tree，用于快速查询
pub struct SimpleDsuOnTree {
    adj: Vec<Vec<usize>>,
    colors: Vec<usize>,
}

impl SimpleDsuOnTree {
    /// 创建简化版实例
    pub fn new(n: usize, colors: Vec<usize>) -> Self {
        SimpleDsuOnTree {
            adj: vec![vec![]; n],
            colors,
        }
    }

    /// 添加边
    pub fn add_edge(&mut self, u: usize, v: usize) {
        self.adj[u].push(v);
        self.adj[v].push(u);
    }

    /// 查询每个子树中不同颜色的数量
    ///
    /// # 复杂度
    /// - 时间: O(n log n)
    /// - 空间: O(n)
    pub fn query_distinct_colors(self) -> Vec<usize> {
        let dsu = DsuOnTree {
            adj: self.adj,
            colors: self.colors,
            subtree_size: vec![],
            heavy_child: vec![],
            keep: vec![],
            freq: HashMap::new(),
            distinct_count: 0,
            ans: vec![],
        };
        dsu.solve(0)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_dsu_on_tree() {
        // 树结构:
        //       0(1)
        //      /   \
        //    1(2)  2(1)
        //   /   \
        // 3(3)  4(2)
        let n = 5;
        let colors = vec![1, 2, 1, 3, 2];
        let mut dsu = DsuOnTree::new(n, colors);

        dsu.add_edge(0, 1);
        dsu.add_edge(0, 2);
        dsu.add_edge(1, 3);
        dsu.add_edge(1, 4);

        let ans = dsu.solve(0);

        // 验证结果
        assert_eq!(ans[3], 1); // 叶子节点，只有颜色3
        assert_eq!(ans[4], 1); // 叶子节点，只有颜色2
        assert_eq!(ans[2], 1); // 叶子节点，只有颜色1
        assert_eq!(ans[1], 2); // 子树包含颜色2,3,2 -> 2种不同颜色
        assert_eq!(ans[0], 3); // 整棵树有3种不同颜色
    }

    #[test]
    fn test_star_tree() {
        // 星形树：根节点连接所有其他节点
        let n = 6;
        let colors = vec![1, 2, 3, 4, 5, 6];
        let mut dsu = DsuOnTree::new(n, colors);

        for i in 1..n {
            dsu.add_edge(0, i);
        }

        let ans = dsu.solve(0);

        assert_eq!(ans[0], 6); // 整棵树6种不同颜色
        for i in 1..n {
            assert_eq!(ans[i], 1); // 每个叶子节点1种颜色
        }
    }

    #[test]
    fn test_chain_tree() {
        // 链状树: 0-1-2-3-4
        let n = 5;
        let colors = vec![1, 1, 2, 2, 1];
        let mut dsu = DsuOnTree::new(n, colors);

        for i in 0..n - 1 {
            dsu.add_edge(i, i + 1);
        }

        let ans = dsu.solve(0);

        // 根节点0的子树包含所有节点
        assert_eq!(ans[0], 2); // 只有2种不同颜色: 1和2
    }

    #[test]
    fn test_same_colors() {
        // 所有节点颜色相同
        let n = 4;
        let colors = vec![5, 5, 5, 5];
        let mut dsu = DsuOnTree::new(n, colors);

        dsu.add_edge(0, 1);
        dsu.add_edge(0, 2);
        dsu.add_edge(2, 3);

        let ans = dsu.solve(0);

        for i in 0..n {
            assert_eq!(ans[i], 1); // 每个子树都只有1种颜色
        }
    }

    #[test]
    fn test_single_node() {
        let n = 1;
        let colors = vec![42];
        let dsu = DsuOnTree::new(n, colors);

        let ans = dsu.solve(0);

        assert_eq!(ans[0], 1);
    }
}
