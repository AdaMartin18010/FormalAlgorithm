//! 点分治 (Centroid Decomposition)
//!
//! 一种树的分治算法，通过递归地选择树的重心将树分解，用于解决路径统计问题。
//!
//! ## 核心思想
//! - 树的重心：删除该节点后，最大子树的大小不超过 n/2
//! - 每次选择当前树的重心作为分治中心
//! - 处理经过重心的所有路径
//! - 递归处理重心分割出的各个子树
//!
//! ## 适用问题
//! - 树中距离为 k 的点对数量
//! - 树中距离不超过 k 的点对数量
//! - 树中最长路径/带权路径问题
//! - 路径上权值和/积满足特定条件的点对
//!
//! ## 复杂度分析
//! - 预处理（找重心）: O(n log n)
//! - 每层处理: O(n)
//! - 总层数: O(log n)
//! - 总时间: O(n log n) 或 O(n log²n) 取决于具体问题
//! - 空间: O(n)
//!
//! 对标: 竞赛编程高级算法

/// 点分治结构
pub struct CentroidDecomposition {
    /// 树的邻接表（目标节点，边权）
    adj: Vec<Vec<(usize, i64)>>,
    /// 子树大小
    subtree_size: Vec<usize>,
    /// 节点是否已被删除（作为重心处理过）
    removed: Vec<bool>,
    /// 节点数量
    n: usize,
    /// 当前答案（根据具体问题修改）
    answer: i64,
}

impl CentroidDecomposition {
    /// 创建点分治结构
    ///
    /// # 参数
    /// - `n`: 节点数量
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn new(n: usize) -> Self {
        CentroidDecomposition {
            adj: vec![vec![]; n],
            subtree_size: vec![0; n],
            removed: vec![false; n],
            n,
            answer: 0,
        }
    }

    /// 添加边（无向树）
    pub fn add_edge(&mut self, u: usize, v: usize, w: i64) {
        self.adj[u].push((v, w));
        self.adj[v].push((u, w));
    }

    /// 计算子树大小
    fn calc_size(&mut self, u: usize, parent: usize) {
        self.subtree_size[u] = 1;
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v != parent && !self.removed[v] {
                self.calc_size(v, u);
                self.subtree_size[u] += self.subtree_size[v];
            }
        }
    }

    /// 找到重心
    fn find_centroid(&self, u: usize, parent: usize, total_size: usize) -> usize {
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v != parent && !self.removed[v] && self.subtree_size[v] > total_size / 2 {
                return self.find_centroid(v, u, total_size);
            }
        }
        u
    }

    /// 收集从 u 出发到子树中所有节点的距离
    fn collect_distances(&self, u: usize, parent: usize, dist: i64, distances: &mut Vec<i64>) {
        distances.push(dist);
        for i in 0..self.adj[u].len() {
            let (v, w) = self.adj[u][i];
            if v != parent && !self.removed[v] {
                self.collect_distances(v, u, dist + w, distances);
            }
        }
    }

    /// 统计距离小于等于 k 的点对数量
    fn count_pairs(&self, distances: &mut [i64], k: i64) -> i64 {
        distances.sort_unstable();
        let mut count = 0i64;
        let mut left = 0usize;
        let mut right = distances.len().saturating_sub(1);

        while left < right {
            if distances[left] + distances[right] <= k {
                count += (right - left) as i64;
                left += 1;
            } else {
                right -= 1;
            }
        }
        count
    }

    /// 处理以重心为中心的路径
    fn process_centroid(&mut self, centroid: usize, k: i64) {
        let mut all_distances: Vec<i64> = vec![0]; // 重心到自身的距离为0

        for i in 0..self.adj[centroid].len() {
            let (v, w) = self.adj[centroid][i];
            if self.removed[v] {
                continue;
            }

            let mut sub_distances: Vec<i64> = Vec::new();
            self.collect_distances(v, centroid, w, &mut sub_distances);

            // 减去同一子树内的非法点对
            let invalid_pairs = self.count_pairs(&mut sub_distances.clone(), k);
            self.answer -= invalid_pairs;

            all_distances.extend(sub_distances);
        }

        // 加上所有经过重心的合法点对
        let valid_pairs = self.count_pairs(&mut all_distances, k);
        self.answer += valid_pairs;
    }

    /// 递归分解
    fn decompose_recursive(&mut self, entry: usize, k: i64) {
        self.calc_size(entry, entry);
        let centroid = self.find_centroid(entry, entry, self.subtree_size[entry]);

        self.process_centroid(centroid, k);
        self.removed[centroid] = true;

        // 递归处理子树
        for i in 0..self.adj[centroid].len() {
            let (v, _) = self.adj[centroid][i];
            if !self.removed[v] {
                self.decompose_recursive(v, k);
            }
        }
    }

    /// 求解树中距离不超过 k 的点对数量
    ///
    /// # 参数
    /// - `k`: 最大距离限制
    ///
    /// # 返回值
    /// 距离不超过 k 的无序点对数量
    ///
    /// # 复杂度
    /// - 时间: O(n log²n)
    /// - 空间: O(n)
    pub fn count_pairs_within_distance(mut self, k: i64) -> i64 {
        if self.n <= 1 {
            return 0;
        }
        self.decompose_recursive(0, k);
        self.answer
    }

    /// 获取当前答案（用于调试）
    pub fn get_answer(&self) -> i64 {
        self.answer
    }
}

/// 带权点分治：用于更复杂的路径统计问题
pub struct WeightedCentroidDecomposition<T> {
    adj: Vec<Vec<(usize, i64)>>,
    subtree_size: Vec<usize>,
    removed: Vec<bool>,
    n: usize,
    /// 自定义处理器
    processor: Box<dyn Fn(&[i64]) -> T>,
    result: T,
}

impl<T: Default + Clone> WeightedCentroidDecomposition<T> {
    /// 创建带权重点分治
    ///
    /// # 参数
    /// - `n`: 节点数量
    /// - `processor`: 自定义距离数组处理器
    pub fn new<F>(n: usize, processor: F) -> Self
    where
        F: Fn(&[i64]) -> T + 'static,
    {
        WeightedCentroidDecomposition {
            adj: vec![vec![]; n],
            subtree_size: vec![0; n],
            removed: vec![false; n],
            n,
            processor: Box::new(processor),
            result: T::default(),
        }
    }

    /// 添加边
    pub fn add_edge(&mut self, u: usize, v: usize, w: i64) {
        self.adj[u].push((v, w));
        self.adj[v].push((u, w));
    }

    fn calc_size(&mut self, u: usize, parent: usize) {
        self.subtree_size[u] = 1;
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v != parent && !self.removed[v] {
                self.calc_size(v, u);
                self.subtree_size[u] += self.subtree_size[v];
            }
        }
    }

    fn find_centroid(&self, u: usize, parent: usize, total_size: usize) -> usize {
        for i in 0..self.adj[u].len() {
            let (v, _) = self.adj[u][i];
            if v != parent && !self.removed[v] && self.subtree_size[v] > total_size / 2 {
                return self.find_centroid(v, u, total_size);
            }
        }
        u
    }

    fn collect_distances(&self, u: usize, parent: usize, dist: i64, distances: &mut Vec<i64>) {
        distances.push(dist);
        for i in 0..self.adj[u].len() {
            let (v, w) = self.adj[u][i];
            if v != parent && !self.removed[v] {
                self.collect_distances(v, u, dist + w, distances);
            }
        }
    }

    fn process_centroid(&mut self, centroid: usize) {
        let mut all_distances: Vec<i64> = vec![0];

        for i in 0..self.adj[centroid].len() {
            let (v, w) = self.adj[centroid][i];
            if self.removed[v] {
                continue;
            }

            let mut sub_distances: Vec<i64> = Vec::new();
            self.collect_distances(v, centroid, w, &mut sub_distances);
            all_distances.extend(sub_distances);
        }

        // 应用自定义处理器
        let centroid_result = (self.processor)(&all_distances);
        self.merge_result(centroid_result);
    }

    fn merge_result(&mut self, value: T) {
        // 默认实现：直接替换，子类可覆盖
        self.result = value;
    }

    fn decompose_recursive(&mut self, entry: usize) {
        self.calc_size(entry, entry);
        let centroid = self.find_centroid(entry, entry, self.subtree_size[entry]);

        self.process_centroid(centroid);
        self.removed[centroid] = true;

        for i in 0..self.adj[centroid].len() {
            let (v, _) = self.adj[centroid][i];
            if !self.removed[v] {
                self.decompose_recursive(v);
            }
        }
    }

    /// 执行分治并返回结果
    pub fn solve(mut self, root: usize) -> T {
        if self.n == 0 {
            return T::default();
        }
        self.decompose_recursive(root);
        self.result
    }
}

/// 点分治工具函数：统计距离恰好为 k 的点对数量
///
/// # 复杂度
/// - 时间: O(n log²n)
/// - 空间: O(n)
pub fn count_pairs_with_exact_distance(
    n: usize,
    edges: &[(usize, usize, i64)],
    target_dist: i64,
) -> i64 {
    let mut cd = CentroidDecomposition::new(n);
    for &(u, v, w) in edges {
        cd.add_edge(u, v, w);
    }

    // 使用容斥原理：≤ k 的数量减去 ≤ k-1 的数量
    let le_k = cd.count_pairs_within_distance(target_dist);
    let le_k_1 = if target_dist > 0 {
        let mut cd2 = CentroidDecomposition::new(n);
        for &(u, v, w) in edges {
            cd2.add_edge(u, v, w);
        }
        cd2.count_pairs_within_distance(target_dist - 1)
    } else {
        0
    };

    le_k - le_k_1
}

/// 点分治工具函数：计算树的最长路径（直径）
///
/// # 复杂度
/// - 时间: O(n)
/// - 空间: O(n)
pub fn tree_diameter(n: usize, edges: &[(usize, usize, i64)]) -> i64 {
    if n <= 1 {
        return 0;
    }

    // 使用两次 BFS/DFS 方法计算直径
    let mut adj: Vec<Vec<(usize, i64)>> = vec![vec![]; n];
    for &(u, v, w) in edges {
        adj[u].push((v, w));
        adj[v].push((u, w));
    }

    fn dfs_farthest(
        adj: &[Vec<(usize, i64)>],
        u: usize,
        parent: usize,
        dist: i64,
    ) -> (usize, i64) {
        let mut result = (u, dist);
        for &(v, w) in &adj[u] {
            if v != parent {
                let candidate = dfs_farthest(adj, v, u, dist + w);
                if candidate.1 > result.1 {
                    result = candidate;
                }
            }
        }
        result
    }

    // 从任意点(0)出发找到最远点
    let (farthest, _) = dfs_farthest(&adj, 0, 0, 0);
    // 从最远点出发找到最远距离
    let (_, diameter) = dfs_farthest(&adj, farthest, farthest, 0);

    diameter
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_centroid_decomposition() {
        // 树结构:
        //       0
        //      / \
        //    1    2
        //   / \
        //  3   4
        // 所有边权为1
        let n = 5;
        let mut cd = CentroidDecomposition::new(n);

        cd.add_edge(0, 1, 1);
        cd.add_edge(0, 2, 1);
        cd.add_edge(1, 3, 1);
        cd.add_edge(1, 4, 1);

        // 统计距离 <= 2 的点对
        let count = cd.count_pairs_within_distance(2);

        // 所有点对: (0,1)=1, (0,2)=1, (0,3)=2, (0,4)=2, (1,2)=2, (1,3)=1, (1,4)=1, (2,3)=3, (2,4)=3, (3,4)=2
        // 距离 <= 2: (0,1), (0,2), (0,3), (0,4), (1,2), (1,3), (1,4), (3,4) = 8对
        assert_eq!(count, 8);
    }

    #[test]
    fn test_star_tree() {
        // 星形树：根节点0连接所有其他节点
        let n = 6;
        let mut cd = CentroidDecomposition::new(n);

        for i in 1..n {
            cd.add_edge(0, i, 1);
        }

        // 统计距离 <= 1 的点对
        let count = cd.count_pairs_within_distance(1);

        // 只有 (0,i) 类型的点对距离为1，共5对
        assert_eq!(count, 5);
    }

    #[test]
    fn test_chain_tree() {
        // 链状树: 0-1-2-3-4，边权为1
        let n = 5;
        let mut cd = CentroidDecomposition::new(n);

        for i in 0..n - 1 {
            cd.add_edge(i, i + 1, 1);
        }

        // 统计距离 <= 2 的点对
        let count = cd.count_pairs_within_distance(2);

        // 点对: (0,1)=1, (0,2)=2, (0,3)=3, (0,4)=4, (1,2)=1, (1,3)=2, (1,4)=3, (2,3)=1, (2,4)=2, (3,4)=1
        // 距离 <= 2: (0,1), (0,2), (1,2), (1,3), (2,3), (2,4), (3,4) = 7对
        assert_eq!(count, 7);
    }

    #[test]
    fn test_weighted_edges() {
        // 带权树
        let n = 4;
        let mut cd = CentroidDecomposition::new(n);

        cd.add_edge(0, 1, 5);
        cd.add_edge(0, 2, 3);
        cd.add_edge(1, 3, 2);

        // 统计距离 <= 5 的点对
        let count = cd.count_pairs_within_distance(5);

        // (0,1)=5, (0,2)=3, (0,3)=7, (1,2)=8, (1,3)=2, (2,3)=10
        // 距离 <= 5: (0,1), (0,2), (1,3) = 3对
        assert_eq!(count, 3);
    }

    #[test]
    fn test_single_node() {
        let n = 1;
        let cd = CentroidDecomposition::new(n);

        let count = cd.count_pairs_within_distance(0);

        // 单个节点没有对
        assert_eq!(count, 0);
    }

    #[test]
    fn test_two_nodes() {
        let n = 2;
        let mut cd = CentroidDecomposition::new(n);

        cd.add_edge(0, 1, 10);

        // 距离 <= 10: 1对
        let count = cd.count_pairs_within_distance(10);
        assert_eq!(count, 1);

        // 距离 <= 5: 0对
        let mut cd2 = CentroidDecomposition::new(n);
        cd2.add_edge(0, 1, 10);
        let count2 = cd2.count_pairs_within_distance(5);
        assert_eq!(count2, 0);
    }

    #[test]
    fn test_tree_diameter() {
        // 树:
        //       0
        //      / \
        //    1    2
        //   /      \
        //  3        4
        // 边权: 0-1=1, 0-2=2, 1-3=3, 2-4=4
        // 最长路径: 3-1-0-2-4 = 1+3+2+4 = 10
        let n = 5;
        let edges = vec![
            (0, 1, 1),
            (0, 2, 2),
            (1, 3, 3),
            (2, 4, 4),
        ];

        let diameter = tree_diameter(n, &edges);
        assert_eq!(diameter, 10);
    }

    #[test]
    fn test_tree_diameter_chain() {
        // 链状树的直径就是整条链
        let n = 5;
        let edges = vec![
            (0, 1, 1),
            (1, 2, 2),
            (2, 3, 3),
            (3, 4, 4),
        ];

        let diameter = tree_diameter(n, &edges);
        assert_eq!(diameter, 10); // 1+2+3+4
    }

    #[test]
    fn test_all_pairs() {
        // 测试所有距离的点对
        let n = 4;
        let mut cd = CentroidDecomposition::new(n);

        // 完全二叉树结构
        cd.add_edge(0, 1, 1);
        cd.add_edge(0, 2, 1);
        cd.add_edge(1, 3, 1);

        // 距离 <= 3（应该是所有点对）
        // 点对: (0,1)=1, (0,2)=1, (0,3)=2, (1,2)=2, (1,3)=1, (2,3)=3
        // 共6对，全部 <= 3
        let count = cd.count_pairs_within_distance(3);
        assert_eq!(count, 6);
    }
}
