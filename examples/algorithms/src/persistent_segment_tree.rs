//! 可持久化线段树（Persistent Segment Tree / 主席树）
//!
//! 可持久化线段树是一种支持版本历史的数据结构，每次修改会创建一个新版本，
//! 同时保留旧版本。常用于区间第K小、历史版本查询等问题。
//!
//! # 核心思想
//! 每次单点修改只影响 O(log n) 个节点，其他节点与旧版本共享。
//! 新版本通过克隆修改路径上的节点实现，空间复杂度为 O(log n) 每次修改。
//!
//! # 时间复杂度
//! - 建树: O(n log n)
//! - 单点修改: O(log n) 时间，O(log n) 空间
//! - 区间查询: O(log n)
//! - 版本切换: O(1)
//!
//! # 空间复杂度
//! - 初始: O(n log n)
//! - 每次修改: 新增 O(log n) 个节点
//! - m次修改后: O((n + m) log n)
//!
//! # 应用场景
//! - 区间第K小/大查询
//! - 历史版本查询
//! - 可撤销的区间操作
//! - 离线处理动态区间问题

use std::rc::Rc;

/// 节点ID（用于版本管理）
pub type NodeId = usize;

/// 可持久化线段树节点
#[derive(Clone, Debug)]
struct Node {
    /// 左子节点
    left: Option<Rc<Node>>,
    /// 右子节点
    right: Option<Rc<Node>>,
    /// 节点值（区间和或其他聚合值）
    value: i64,
    /// 区间左边界
    l: usize,
    /// 区间右边界
    r: usize,
}

impl Node {
    /// 创建叶子节点
    fn new_leaf(value: i64, pos: usize) -> Self {
        Node {
            left: None,
            right: None,
            value,
            l: pos,
            r: pos,
        }
    }

    /// 创建内部节点
    fn new_internal(left: Rc<Node>, right: Rc<Node>, l: usize, r: usize) -> Self {
        let value = left.value + right.value;
        Node {
            left: Some(left),
            right: Some(right),
            value,
            l,
            r,
        }
    }

    /// 创建空节点（值为0）
    fn empty(l: usize, r: usize) -> Self {
        Node {
            left: None,
            right: None,
            value: 0,
            l,
            r,
        }
    }

    /// 是否是叶子节点
    fn is_leaf(&self) -> bool {
        self.l == self.r
    }
}

/// 可持久化线段树
pub struct PersistentSegmentTree {
    /// 所有版本（根节点）
    versions: Vec<Option<Rc<Node>>>,
    /// 原始数组长度
    n: usize,
}

/// 查询结果
#[derive(Debug, Clone)]
pub struct QueryResult {
    pub sum: i64,
    pub count: usize,
}

impl PersistentSegmentTree {
    /// 创建新的可持久化线段树
    ///
    /// # 参数
    /// - `arr`: 初始数组
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::PersistentSegmentTree;
    /// let pst = PersistentSegmentTree::new(&[1, 2, 3, 4, 5]);
    /// ```
    pub fn new(arr: &[i64]) -> Self {
        let n = arr.len();
        if n == 0 {
            return PersistentSegmentTree {
                versions: vec![None],
                n: 0,
            };
        }

        let root = Self::build(arr, 0, n - 1);
        PersistentSegmentTree {
            versions: vec![Some(root)],
            n,
        }
    }

    /// 递归构建线段树
    fn build(arr: &[i64], l: usize, r: usize) -> Rc<Node> {
        if l == r {
            return Rc::new(Node::new_leaf(arr[l], l));
        }

        let mid = (l + r) / 2;
        let left = Self::build(arr, l, mid);
        let right = Self::build(arr, mid + 1, r);

        Rc::new(Node::new_internal(left, right, l, r))
    }

    /// 单点修改：在指定位置增加一个值
    ///
    /// # 参数
    /// - `version`: 基于的版本号
    /// - `pos`: 修改位置
    /// - `delta`: 增量
    ///
    /// # 返回值
    /// 新版本号
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::PersistentSegmentTree;
    /// let mut pst = PersistentSegmentTree::new(&[1, 2, 3, 4, 5]);
    /// let v1 = pst.update(0, 2, 10); // 版本0的位置2加10
    /// ```
    pub fn update(&mut self, version: usize, pos: usize, delta: i64) -> usize {
        assert!(version < self.versions.len(), "版本号不存在");
        assert!(pos < self.n, "位置超出范围");

        let new_root = self.update_recursive(self.versions[version].clone(), pos, delta, 0, self.n - 1);
        self.versions.push(Some(new_root));
        self.versions.len() - 1
    }

    /// 递归修改
    fn update_recursive(
        &self,
        node: Option<Rc<Node>>,
        pos: usize,
        delta: i64,
        l: usize,
        r: usize,
    ) -> Rc<Node> {
        // 如果当前区间不包含目标位置，创建空节点并继续
        let node = node.unwrap_or_else(|| Rc::new(Node::empty(l, r)));

        if l == r {
            // 叶子节点，创建新节点
            return Rc::new(Node::new_leaf(node.value + delta, l));
        }

        let mid = (l + r) / 2;

        let new_left = if pos <= mid {
            Some(self.update_recursive(node.left.clone(), pos, delta, l, mid))
        } else {
            node.left.clone()
        };

        let new_right = if pos > mid {
            Some(self.update_recursive(node.right.clone(), pos, delta, mid + 1, r))
        } else {
            node.right.clone()
        };

        Rc::new(Node {
            left: new_left,
            right: new_right,
            value: node.value + delta,
            l,
            r,
        })
    }

    /// 单点设置值
    ///
    /// # 参数
    /// - `version`: 基于的版本号
    /// - `pos`: 位置
    /// - `value`: 新值
    ///
    /// # 返回值
    /// 新版本号
    pub fn set(&mut self, version: usize, pos: usize, value: i64) -> usize {
        let current = self.point_query(version, pos);
        let delta = value - current;
        self.update(version, pos, delta)
    }

    /// 区间查询
    ///
    /// # 参数
    /// - `version`: 版本号
    /// - `ql`: 查询左边界
    /// - `qr`: 查询右边界
    ///
    /// # 返回值
    /// 区间和
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::PersistentSegmentTree;
    /// let pst = PersistentSegmentTree::new(&[1, 2, 3, 4, 5]);
    /// let sum = pst.range_query(0, 1, 3); // 查询版本0的[1,3]区间和
    /// assert_eq!(sum, 9); // 2 + 3 + 4
    /// ```
    pub fn range_query(&self, version: usize, ql: usize, qr: usize) -> i64 {
        assert!(version < self.versions.len(), "版本号不存在");
        assert!(ql <= qr && qr < self.n, "查询范围无效");

        self.query_recursive(&self.versions[version], ql, qr, 0, self.n - 1)
    }

    /// 递归查询
    fn query_recursive(
        &self,
        node: &Option<Rc<Node>>,
        ql: usize,
        qr: usize,
        l: usize,
        r: usize,
    ) -> i64 {
        if let Some(n) = node {
            // 完全包含
            if ql <= l && r <= qr {
                return n.value;
            }

            // 无交集
            if r < ql || l > qr {
                return 0;
            }

            let mid = (l + r) / 2;
            let left_sum = self.query_recursive(&n.left, ql, qr, l, mid);
            let right_sum = self.query_recursive(&n.right, ql, qr, mid + 1, r);

            left_sum + right_sum
        } else {
            0
        }
    }

    /// 单点查询
    pub fn point_query(&self, version: usize, pos: usize) -> i64 {
        self.range_query(version, pos, pos)
    }

    /// 查询区间第K小（假设数组存储的是离散化后的值）
    ///
    /// # 参数
    /// - `version_l`: 左版本（通常是version-1）
    /// - `version_r`: 右版本
    /// - `k`: 第K小（1-based）
    ///
    /// # 返回值
    /// 第K小的值（离散化前的原始值需要通过映射表转换）
    ///
    /// # 说明
    /// 用于静态区间第K小问题，需配合离散化使用
    pub fn kth_smallest(&self, version_l: usize, version_r: usize, k: usize) -> Option<i64> {
        assert!(k > 0, "k must be positive");
        assert!(version_l < self.versions.len() && version_r < self.versions.len());

        self.kth_recursive(
            &self.versions[version_l],
            &self.versions[version_r],
            k,
            0,
            self.n - 1,
        )
    }

    /// 递归查找第K小
    fn kth_recursive(
        &self,
        node_l: &Option<Rc<Node>>,
        node_r: &Option<Rc<Node>>,
        k: usize,
        l: usize,
        r: usize,
    ) -> Option<i64> {
        if l == r {
            return Some(l as i64);
        }

        let left_count_r = node_r.as_ref().and_then(|n| n.left.as_ref()).map(|n| n.value as usize).unwrap_or(0);
        let left_count_l = node_l.as_ref().and_then(|n| n.left.as_ref()).map(|n| n.value as usize).unwrap_or(0);
        let left_count = left_count_r - left_count_l;

        let mid = (l + r) / 2;

        if k <= left_count {
            let left_l = node_l.as_ref().and_then(|n| n.left.clone());
            let left_r = node_r.as_ref().and_then(|n| n.left.clone());
            self.kth_recursive(&left_l, &left_r, k, l, mid)
        } else {
            let right_l = node_l.as_ref().and_then(|n| n.right.clone());
            let right_r = node_r.as_ref().and_then(|n| n.right.clone());
            self.kth_recursive(&right_l, &right_r, k - left_count, mid + 1, r)
        }
    }

    /// 获取版本数量
    pub fn version_count(&self) -> usize {
        self.versions.len()
    }

    /// 获取当前最新版本号
    pub fn latest_version(&self) -> usize {
        self.versions.len() - 1
    }

    /// 比较两个版本的差异
    ///
    /// # 返回值
    /// (位置, 旧值, 新值) 的列表
    pub fn diff(&self, version_a: usize, version_b: usize) -> Vec<(usize, i64, i64)> {
        let mut result = Vec::new();

        for i in 0..self.n {
            let val_a = self.point_query(version_a, i);
            let val_b = self.point_query(version_b, i);
            if val_a != val_b {
                result.push((i, val_a, val_b));
            }
        }

        result
    }

    /// 回滚到指定版本（创建新副本）
    pub fn rollback(&mut self, version: usize) -> usize {
        assert!(version < self.versions.len());

        // 复制指定版本的根节点作为新版本
        self.versions.push(self.versions[version].clone());
        self.versions.len() - 1
    }

    /// 输出指定版本的数组状态
    pub fn to_vec(&self, version: usize) -> Vec<i64> {
        assert!(version < self.versions.len());

        let mut result = Vec::with_capacity(self.n);
        for i in 0..self.n {
            result.push(self.point_query(version, i));
        }
        result
    }
}

/// 用于区间第K小的辅助结构（配合离散化）
pub struct KthPersistentSegmentTree {
    /// 离散化映射：原始值 -> 离散化值（已排序）
    sorted_values: Vec<i64>,
    /// 值到索引的映射
    value_to_idx: std::collections::HashMap<i64, usize>,
    /// 可持久化线段树（存储频率）
    pst: PersistentSegmentTree,
    /// 前缀版本映射：prefix_versions[i] 表示 arr[0..i-1] 对应的 PST 版本号
    prefix_versions: Vec<usize>,
    /// 当前数组状态（用于支持单点更新）
    current_arr: Vec<i64>,
}

impl KthPersistentSegmentTree {
    /// 从原始数组创建（自动离散化）
    pub fn new(arr: &[i64]) -> Self {
        // 离散化
        let mut sorted_values: Vec<i64> = arr.iter().cloned().collect();
        sorted_values.sort_unstable();
        sorted_values.dedup();

        let mut value_to_idx = std::collections::HashMap::new();
        for (idx, &val) in sorted_values.iter().enumerate() {
            value_to_idx.insert(val, idx);
        }

        // 建立空的可持久化线段树，用于统计各离散值的频率
        let mut pst = PersistentSegmentTree::new(&vec![0i64; sorted_values.len()]);

        // 建立前缀版本：prefix_versions[i] 包含 arr[0..i-1] 中各值的频率
        let mut prefix_versions = vec![0]; // version 0 对应空数组
        for &x in arr {
            let idx = *value_to_idx.get(&x).unwrap();
            let new_version = pst.update(*prefix_versions.last().unwrap(), idx, 1);
            prefix_versions.push(new_version);
        }

        KthPersistentSegmentTree {
            sorted_values,
            value_to_idx,
            pst,
            prefix_versions,
            current_arr: arr.to_vec(),
        }
    }

    /// 单点更新（将 arr[pos] 修改为 new_value）
    ///
    /// 修正说明：原实现错误地直接调用 PST 的 set 方法（把频率树当值树用），
    /// 现改为先减少旧值频率、再增加新值频率。
    pub fn update(&mut self, pos: usize, new_value: i64) -> usize {
        assert!(pos < self.current_arr.len(), "位置超出范围");
        let old_value = self.current_arr[pos];
        let old_idx = *self.value_to_idx.get(&old_value).unwrap();
        let new_idx = *self.value_to_idx.get(&new_value).unwrap();

        let last_version = *self.prefix_versions.last().unwrap();
        let v1 = self.pst.update(last_version, old_idx, -1);
        let v2 = self.pst.update(v1, new_idx, 1);

        self.current_arr[pos] = new_value;
        self.prefix_versions.push(v2);
        v2
    }

    /// 查询区间 [l, r]（0-based，包含两端）的第K小
    ///
    /// 修正说明：原实现未建立前缀版本，导致 kth_smallest 计算错误。
    /// 现通过 prefix_versions 将数组区间 [l, r] 映射到 PST 的两个版本做差分。
    pub fn query_kth(&self, l: usize, r: usize, k: usize) -> Option<i64> {
        assert!(l <= r && r < self.current_arr.len(), "查询范围无效");
        assert!(k > 0, "k must be positive");

        self.pst
            .kth_smallest(self.prefix_versions[l], self.prefix_versions[r + 1], k)
            .map(|idx| self.sorted_values[idx as usize])
    }

    /// 获取当前版本数
    pub fn version_count(&self) -> usize {
        self.prefix_versions.len()
    }
}

/// 辅助函数：快速创建可持久化线段树
pub fn persistent_segment_tree(arr: &[i64]) -> PersistentSegmentTree {
    PersistentSegmentTree::new(arr)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut pst = PersistentSegmentTree::new(&[1, 2, 3, 4, 5]);

        // 版本0: [1, 2, 3, 4, 5]
        assert_eq!(pst.range_query(0, 0, 4), 15);
        assert_eq!(pst.range_query(0, 1, 3), 9);

        // 创建版本1: 位置2加10 -> [1, 2, 13, 4, 5]
        let v1 = pst.update(0, 2, 10);
        assert_eq!(v1, 1);
        assert_eq!(pst.range_query(v1, 2, 2), 13);
        assert_eq!(pst.range_query(v1, 0, 4), 25);

        // 版本0保持不变
        assert_eq!(pst.range_query(0, 2, 2), 3);
    }

    #[test]
    fn test_multiple_versions() {
        let mut pst = PersistentSegmentTree::new(&[0, 0, 0, 0, 0]);

        // v0: [0, 0, 0, 0, 0]
        // v1: [1, 0, 0, 0, 0]
        let v1 = pst.update(0, 0, 1);
        // v2: [1, 2, 0, 0, 0]
        let v2 = pst.update(v1, 1, 2);
        // v3: [1, 2, 3, 0, 0]
        let v3 = pst.update(v2, 2, 3);

        assert_eq!(pst.range_query(v1, 0, 4), 1);
        assert_eq!(pst.range_query(v2, 0, 4), 3);
        assert_eq!(pst.range_query(v3, 0, 4), 6);
    }

    #[test]
    fn test_set_operation() {
        let mut pst = PersistentSegmentTree::new(&[1, 2, 3]);

        // v1: [1, 5, 3]
        let v1 = pst.set(0, 1, 5);
        assert_eq!(pst.point_query(v1, 1), 5);
        assert_eq!(pst.point_query(0, 1), 2); // v0 不变
    }

    #[test]
    fn test_rollback() {
        let mut pst = PersistentSegmentTree::new(&[1, 2, 3, 4, 5]);

        let v1 = pst.update(0, 0, 10); // v1: [11, 2, 3, 4, 5]
        let v2 = pst.update(v1, 1, 10); // v2: [11, 12, 3, 4, 5]

        // 回滚到v0
        let v3 = pst.rollback(0);
        assert_eq!(pst.point_query(v3, 0), 1);
        assert_eq!(pst.point_query(v3, 1), 2);
    }

    #[test]
    fn test_diff() {
        let mut pst = PersistentSegmentTree::new(&[1, 2, 3]);

        let v1 = pst.set(0, 1, 5);
        let diff = pst.diff(0, v1);

        assert_eq!(diff.len(), 1);
        assert_eq!(diff[0], (1, 2, 5));
    }

    #[test]
    fn test_to_vec() {
        let mut pst = PersistentSegmentTree::new(&[1, 2, 3]);
        let v1 = pst.update(0, 0, 10);

        assert_eq!(pst.to_vec(0), vec![1, 2, 3]);
        assert_eq!(pst.to_vec(v1), vec![11, 2, 3]);
    }

    #[test]
    fn test_kth_smallest_simple() {
        // 注意：这个功能需要特殊构造的数据结构
        // 这里测试基本功能
        let pst = PersistentSegmentTree::new(&[0, 1, 2, 2, 3]);

        // 测试基本查询
        assert_eq!(pst.range_query(0, 0, 4), 8);
    }

    #[test]
    fn test_kth_pst() {
        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        let kpst = KthPersistentSegmentTree::new(&arr);

        // 排序后: [1, 1, 2, 3, 4, 5, 6, 9]
        // 查询整个数组的第K小
        assert_eq!(kpst.query_kth(0, arr.len() - 1, 1), Some(1));
        assert_eq!(kpst.query_kth(0, arr.len() - 1, 3), Some(2));
    }

    #[test]
    fn test_empty_array() {
        let pst = PersistentSegmentTree::new(&[]);
        assert_eq!(pst.version_count(), 1);
    }

    #[test]
    fn test_single_element() {
        let mut pst = PersistentSegmentTree::new(&[5]);

        assert_eq!(pst.range_query(0, 0, 0), 5);

        let v1 = pst.update(0, 0, 3);
        assert_eq!(pst.range_query(v1, 0, 0), 8);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn version_control_example() {
        println!("\n=== 版本控制示例 ===");

        let mut pst = PersistentSegmentTree::new(&[10, 20, 30, 40, 50]);
        println!("初始版本 (v0): {:?}", pst.to_vec(0));

        // v1: 位置2增加100
        let v1 = pst.update(0, 2, 100);
        println!("v1 (位置2+100): {:?}", pst.to_vec(v1));

        // v2: 位置0减少5
        let v2 = pst.update(v1, 0, -5);
        println!("v2 (位置0-5): {:?}", pst.to_vec(v2));

        // v3: 基于v0创建（分支）
        let v3 = pst.update(0, 4, 50);
        println!("v3 (基于v0, 位置4+50): {:?}", pst.to_vec(v3));

        // 查询历史版本
        println!("\n历史版本查询:");
        println!("v0区间[1,3]和: {}", pst.range_query(0, 1, 3));
        println!("v1区间[1,3]和: {}", pst.range_query(1, 1, 3));
        println!("v2区间[0,4]和: {}", pst.range_query(2, 0, 4));

        // 版本差异
        println!("\nv0和v2的差异: {:?}", pst.diff(0, 2));
    }

    #[test]
    fn range_kth_example() {
        println!("\n=== 区间第K小示例 ===");

        let arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
        println!("原始数组: {:?}", arr);

        let kpst = KthPersistentSegmentTree::new(&arr);
        println!("离散化后排序: {:?}", kpst.sorted_values);

        // 查询整个数组的第K小
        for k in 1..=3 {
            if let Some(val) = kpst.query_kth(0, arr.len() - 1, k) {
                println!("整个数组第{}小: {}", k, val);
            }
        }
    }

    #[test]
    fn undo_operations_example() {
        println!("\n=== 可撤销操作示例 ===");

        let mut pst = PersistentSegmentTree::new(&[0; 5]);
        println!("初始: {:?}", pst.to_vec(0));

        // 一系列操作
        let mut current = 0;
        for i in 0..5 {
            current = pst.update(current, i, (i + 1) as i64 * 10);
            println!("操作{}后 (位置{}+{}): {:?}",
                     i + 1, i, (i + 1) * 10, pst.to_vec(current));
        }

        // 回滚到初始版本
        let rollback = pst.rollback(0);
        println!("回滚后: {:?}", pst.to_vec(rollback));

        // 从回滚点继续操作
        let new_version = pst.update(rollback, 0, 100);
        println!("新操作后: {:?}", pst.to_vec(new_version));
    }
}
