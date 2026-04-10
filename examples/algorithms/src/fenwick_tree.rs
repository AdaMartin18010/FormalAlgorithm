//! 树状数组 (Fenwick Tree / Binary Indexed Tree)
//!
//! 树状数组是一种高效支持单点更新和区间查询的数据结构，
//! 由Peter M. Fenwick在1994年提出。
//!
//! # 核心特性
//! - **单点更新**: O(log n)
//! - **前缀和查询**: O(log n)
//! - **区间查询**: O(log n)（通过两个前缀和相减）
//! - **空间复杂度**: O(n)
//!
//! # 与线段树的对比
//! | 特性 | 树状数组 | 线段树 |
//! |------|---------|--------|
//! | 单点更新 | O(log n) | O(log n) |
//! | 区间查询 | O(log n) | O(log n) |
//! | 区间更新 | 需配合差分 | 原生支持(懒标记) |
//! | 代码量 | 少 | 较多 |
//! | 适用场景 | 单点更新+区间查询 | 复杂的区间操作 |
//!
//! # 应用场景
//! - 动态前缀和计算
//! - 区间频率统计
//! - 逆序对计数
//! - 多维数据处理

/// 树状数组 (Fenwick Tree)
///
/// 树状数组维护一个数组，支持高效的单点更新和前缀和查询。
///
/// # 内部表示
///
/// 树状数组使用一个数组`tree`，其中：
/// - `tree[i]` 存储区间 `[i - lowbit(i) + 1, i]` 的和
/// - `lowbit(i) = i & (-i)` 表示i的最低位1所代表的值
///
/// # 示例
///
/// ```
/// use formal_algorithms::fenwick_tree::FenwickTree;
///
/// let mut ft = FenwickTree::new(5);
/// ft.update(1, 5);  // 在位置1增加5
/// ft.update(2, 3);  // 在位置2增加3
/// ft.update(3, 7);  // 在位置3增加7
///
/// assert_eq!(ft.query(3), 15);  // 前缀和: 5 + 3 + 7 = 15
/// assert_eq!(ft.range_query(2, 3), 10);  // 区间和: 3 + 7 = 10
/// ```
#[derive(Debug, Clone)]
pub struct FenwickTree {
    /// 树状数组存储（1-indexed）
    tree: Vec<i64>,
    /// 数组大小
    n: usize,
}

impl FenwickTree {
    /// 创建指定大小的树状数组（初始值为0）
    ///
    /// # 参数
    /// - `n`: 数组大小
    ///
    /// # 复杂度
    /// - **时间**: O(n)
    /// - **空间**: O(n)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let ft = FenwickTree::new(10);
    /// ```
    pub fn new(n: usize) -> Self {
        FenwickTree {
            tree: vec![0; n + 1], // 1-indexed，所以分配n+1
            n,
        }
    }

    /// 从数组构建树状数组
    ///
    /// # 参数
    /// - `arr`: 初始数组
    ///
    /// # 复杂度
    /// - **时间**: O(n log n)（可通过O(n)优化）
    /// - **空间**: O(n)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let ft = FenwickTree::from_vec(&[1, 2, 3, 4, 5]);
    /// assert_eq!(ft.query(3), 6);  // 1 + 2 + 3 = 6
    /// ```
    pub fn from_vec(arr: &[i64]) -> Self {
        let n = arr.len();
        let mut ft = FenwickTree::new(n);

        for (i, &val) in arr.iter().enumerate() {
            ft.update(i + 1, val);
        }

        ft
    }

    /// 从数组O(n)构建树状数组
    ///
    /// 使用更高效的O(n)构建方法
    ///
    /// # 复杂度
    /// - **时间**: O(n)
    /// - **空间**: O(n)
    pub fn build(arr: &[i64]) -> Self {
        let n = arr.len();
        let mut tree = vec![0i64; n + 1];

        // 复制原数组到tree
        for i in 1..=n {
            tree[i] = arr[i - 1];
        }

        // 构建树状数组
        for i in 1..=n {
            let j = i + (i & i.wrapping_neg());
            if j <= n {
                tree[j] += tree[i];
            }
        }

        FenwickTree { tree, n }
    }

    /// 获取lowbit值
    ///
    /// lowbit(x) = x & (-x)，表示x的最低位1所代表的值
    ///
    /// # 示例
    /// - lowbit(6) = lowbit(110₂) = 2
    /// - lowbit(8) = lowbit(1000₂) = 8
    #[inline]
    fn lowbit(x: usize) -> usize {
        x & x.wrapping_neg()
    }

    /// 在指定位置增加一个值（单点更新）
    ///
    /// # 参数
    /// - `idx`: 位置（1-indexed）
    /// - `delta`: 增加的值
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    /// - **空间**: O(1)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let mut ft = FenwickTree::new(5);
    /// ft.update(1, 10);
    /// ft.update(3, 5);
    /// assert_eq!(ft.query(3), 15);
    /// ```
    pub fn update(&mut self, idx: usize, delta: i64) {
        assert!(idx >= 1 && idx <= self.n, "Index out of bounds");

        let mut i = idx;
        while i <= self.n {
            self.tree[i] += delta;
            i += Self::lowbit(i);
        }
    }

    /// 将指定位置的值设置为新值
    ///
    /// # 参数
    /// - `idx`: 位置（1-indexed）
    /// - `value`: 新值
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    pub fn set(&mut self, idx: usize, value: i64) {
        let current = self.get(idx);
        self.update(idx, value - current);
    }

    /// 获取指定位置的当前值
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    pub fn get(&self, idx: usize) -> i64 {
        self.range_query(idx, idx)
    }

    /// 查询前缀和 [1, idx]
    ///
    /// # 参数
    /// - `idx`: 结束位置（1-indexed）
    ///
    /// # 返回值
    /// 返回数组[1..idx]的和
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let mut ft = FenwickTree::new(5);
    /// ft.update(1, 1);
    /// ft.update(2, 2);
    /// ft.update(3, 3);
    /// assert_eq!(ft.query(3), 6);  // 1 + 2 + 3
    /// ```
    pub fn query(&self, idx: usize) -> i64 {
        if idx == 0 {
            return 0;
        }
        assert!(idx <= self.n, "Index out of bounds");

        let mut sum = 0i64;
        let mut i = idx;
        while i > 0 {
            sum += self.tree[i];
            i -= Self::lowbit(i);
        }
        sum
    }

    /// 查询区间和 [left, right]
    ///
    /// # 参数
    /// - `left`: 左边界（1-indexed，包含）
    /// - `right`: 右边界（1-indexed，包含）
    ///
    /// # 返回值
    /// 返回数组[left..right]的和
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let mut ft = FenwickTree::new(5);
    /// ft.update(1, 1);
    /// ft.update(2, 2);
    /// ft.update(3, 3);
    /// ft.update(4, 4);
    /// assert_eq!(ft.range_query(2, 4), 9);  // 2 + 3 + 4
    /// ```
    pub fn range_query(&self, left: usize, right: usize) -> i64 {
        assert!(left >= 1 && right <= self.n && left <= right, "Invalid range");
        self.query(right) - self.query(left - 1)
    }

    /// 查找前缀和首次大于等于target的最小下标
    ///
    /// 要求所有元素非负
    ///
    /// # 参数
    /// - `target`: 目标前缀和
    ///
    /// # 返回值
    /// 如果存在，返回最小下标；否则返回None
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::fenwick_tree::FenwickTree;
    /// let mut ft = FenwickTree::new(5);
    /// ft.update(1, 1);
    /// ft.update(2, 2);
    /// ft.update(3, 3);
    /// ft.update(4, 4);
    /// // 前缀和: [1, 3, 6, 10, ...]
    /// assert_eq!(ft.find_kth(3), Some(2));  // 前缀和>=3的最小下标是2
    /// assert_eq!(ft.find_kth(7), Some(4));  // 前缀和>=7的最小下标是4
    /// ```
    pub fn find_kth(&self, mut target: i64) -> Option<usize> {
        if target <= 0 {
            return None;
        }

        let mut idx = 0usize;
        let mut bit_mask = 1usize << (self.n.ilog2() as usize);

        while bit_mask > 0 {
            let t = idx + bit_mask;
            if t <= self.n && self.tree[t] < target {
                target -= self.tree[t];
                idx = t;
            }
            bit_mask >>= 1;
        }

        if idx < self.n {
            Some(idx + 1)
        } else {
            None
        }
    }

    /// 获取数组大小
    pub fn len(&self) -> usize {
        self.n
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.n == 0
    }
}

/// 支持区间更新的树状数组（差分思想）
///
/// 通过维护差分数组，实现：
/// - 区间增加：O(log n)
/// - 单点查询：O(log n)
#[derive(Debug, Clone)]
pub struct RangeUpdateFenwickTree {
    /// 差分树状数组
    bit1: FenwickTree,
    bit2: FenwickTree,
}

impl RangeUpdateFenwickTree {
    /// 创建指定大小的区间更新树状数组
    pub fn new(n: usize) -> Self {
        RangeUpdateFenwickTree {
            bit1: FenwickTree::new(n),
            bit2: FenwickTree::new(n),
        }
    }

    /// 区间增加 [l, r] 增加 val
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    pub fn range_add(&mut self, l: usize, r: usize, val: i64) {
        Self::internal_add(&mut self.bit1, l, val);
        Self::internal_add(&mut self.bit1, r + 1, -val);
        Self::internal_add(&mut self.bit2, l, val * (l as i64 - 1));
        Self::internal_add(&mut self.bit2, r + 1, -val * (r as i64));
    }

    fn internal_add(bit: &mut FenwickTree, idx: usize, val: i64) {
        bit.update(idx, val);
    }

    /// 前缀和查询
    fn prefix_sum(&self, idx: usize) -> i64 {
        self.bit1.query(idx) * (idx as i64) - self.bit2.query(idx)
    }

    /// 单点查询
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    pub fn point_query(&self, idx: usize) -> i64 {
        self.prefix_sum(idx) - self.prefix_sum(idx - 1)
    }

    /// 区间查询 [l, r]
    ///
    /// # 复杂度
    /// - **时间**: O(log n)
    pub fn range_query(&self, l: usize, r: usize) -> i64 {
        self.prefix_sum(r) - self.prefix_sum(l - 1)
    }
}

/// 逆序对计数
///
/// 使用树状数组统计数组中的逆序对数量
///
/// # 复杂度
/// - **时间**: O(n log n)
/// - **空间**: O(n)
///
/// # 示例
///
/// ```
/// use formal_algorithms::fenwick_tree::count_inversions;
/// let arr = vec![3, 1, 4, 1, 5];
/// let inversions = count_inversions(&arr);
/// assert_eq!(inversions, 3);  // (3,1), (3,1), (4,1)
/// ```
pub fn count_inversions(arr: &[i64]) -> i64 {
    if arr.is_empty() {
        return 0;
    }

    // 离散化
    let mut sorted: Vec<i64> = arr.to_vec();
    sorted.sort_unstable();
    sorted.dedup();

    let get_rank = |x: i64| -> usize {
        sorted.binary_search(&x).unwrap() + 1
    };

    let mut bit = FenwickTree::new(sorted.len());
    let mut inversions = 0i64;

    // 从右向左遍历
    for i in (0..arr.len()).rev() {
        let rank = get_rank(arr[i]);
        // 查询已经遍历过的、比当前元素小的元素个数
        inversions += bit.query(rank - 1);
        bit.update(rank, 1);
    }

    inversions
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut ft = FenwickTree::new(5);

        ft.update(1, 1);
        ft.update(2, 2);
        ft.update(3, 3);
        ft.update(4, 4);
        ft.update(5, 5);

        // 测试前缀和
        assert_eq!(ft.query(1), 1);
        assert_eq!(ft.query(2), 3);   // 1 + 2
        assert_eq!(ft.query(3), 6);   // 1 + 2 + 3
        assert_eq!(ft.query(4), 10);  // 1 + 2 + 3 + 4
        assert_eq!(ft.query(5), 15);  // 1 + 2 + 3 + 4 + 5
    }

    #[test]
    fn test_range_query() {
        let mut ft = FenwickTree::new(5);

        ft.update(1, 1);
        ft.update(2, 2);
        ft.update(3, 3);
        ft.update(4, 4);
        ft.update(5, 5);

        // 测试区间查询
        assert_eq!(ft.range_query(1, 3), 6);   // 1 + 2 + 3
        assert_eq!(ft.range_query(2, 4), 9);   // 2 + 3 + 4
        assert_eq!(ft.range_query(3, 5), 12);  // 3 + 4 + 5
        assert_eq!(ft.range_query(1, 5), 15);  // 总和
    }

    #[test]
    fn test_from_vec() {
        let ft = FenwickTree::from_vec(&[1, 2, 3, 4, 5]);

        assert_eq!(ft.query(3), 6);
        assert_eq!(ft.range_query(2, 4), 9);
    }

    #[test]
    fn test_build() {
        let ft = FenwickTree::build(&[1, 2, 3, 4, 5]);

        assert_eq!(ft.query(3), 6);
        assert_eq!(ft.range_query(2, 4), 9);
    }

    #[test]
    fn test_set_and_get() {
        let mut ft = FenwickTree::from_vec(&[1, 2, 3, 4, 5]);

        assert_eq!(ft.get(3), 3);

        ft.set(3, 10);
        assert_eq!(ft.get(3), 10);
        assert_eq!(ft.query(3), 13);  // 1 + 2 + 10
    }

    #[test]
    fn test_find_kth() {
        let mut ft = FenwickTree::new(5);

        ft.update(1, 1);
        ft.update(2, 2);
        ft.update(3, 3);
        ft.update(4, 4);

        // 前缀和: [1, 3, 6, 10]
        assert_eq!(ft.find_kth(1), Some(1));
        assert_eq!(ft.find_kth(2), Some(2));
        assert_eq!(ft.find_kth(3), Some(2));
        assert_eq!(ft.find_kth(4), Some(3));
        assert_eq!(ft.find_kth(6), Some(3));
        assert_eq!(ft.find_kth(7), Some(4));
        assert_eq!(ft.find_kth(10), Some(4));
        assert_eq!(ft.find_kth(11), None);
    }

    #[test]
    fn test_negative_numbers() {
        let mut ft = FenwickTree::new(5);

        ft.update(1, 5);
        ft.update(2, -3);
        ft.update(3, 2);
        ft.update(4, -1);

        assert_eq!(ft.query(4), 3);  // 5 - 3 + 2 - 1
        assert_eq!(ft.range_query(2, 3), -1);  // -3 + 2
    }

    #[test]
    fn test_large_array() {
        let n = 100000;
        let mut ft = FenwickTree::new(n);

        for i in 1..=n {
            ft.update(i, i as i64);
        }

        let expected_sum: i64 = (1..=n).map(|x| x as i64).sum();
        assert_eq!(ft.query(n), expected_sum);
    }

    #[test]
    fn test_count_inversions() {
        // 基本测试
        assert_eq!(count_inversions(&[1, 2, 3, 4, 5]), 0);
        assert_eq!(count_inversions(&[5, 4, 3, 2, 1]), 10);  // 5*4/2
        assert_eq!(count_inversions(&[3, 1, 4, 1, 5]), 3);

        // 重复元素
        assert_eq!(count_inversions(&[1, 1, 1, 1]), 0);
        assert_eq!(count_inversions(&[2, 2, 1, 1]), 4);

        // 空数组和单元素
        assert_eq!(count_inversions(&[]), 0);
        assert_eq!(count_inversions(&[1]), 0);
    }

    #[test]
    fn test_range_update_fenwick() {
        let mut ft = RangeUpdateFenwickTree::new(5);

        // 区间增加
        ft.range_add(1, 3, 2);  // [1,3] += 2
        ft.range_add(2, 4, 3);  // [2,4] += 3

        // 结果: [2, 5, 5, 3, 0]
        assert_eq!(ft.point_query(1), 2);
        assert_eq!(ft.point_query(2), 5);
        assert_eq!(ft.point_query(3), 5);
        assert_eq!(ft.point_query(4), 3);
        assert_eq!(ft.point_query(5), 0);

        // 区间查询
        assert_eq!(ft.range_query(1, 3), 12);  // 2 + 5 + 5
        assert_eq!(ft.range_query(2, 4), 13);  // 5 + 5 + 3
    }

    #[test]
    fn test_edge_cases() {
        // 查询边界
        let mut ft = FenwickTree::new(5);
        ft.update(1, 10);

        assert_eq!(ft.query(0), 0);
        assert_eq!(ft.query(1), 10);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 动态前缀和
    pub fn example_dynamic_prefix_sum() {
        println!("=== 动态前缀和示例 ===");

        let mut ft = FenwickTree::new(10);

        // 模拟数组: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        println!("初始数组: [0; 10]");

        // 单点更新
        ft.update(3, 5);
        println!("update(3, 5) -> 位置3增加5");
        println!("前缀和 query(5) = {}", ft.query(5));

        ft.update(5, 3);
        println!("update(5, 3) -> 位置5增加3");
        println!("前缀和 query(5) = {}", ft.query(5));

        ft.update(7, 2);
        println!("update(7, 2) -> 位置7增加2");

        // 区间查询
        println!("区间和 [3, 7] = {}", ft.range_query(3, 7));
        println!("区间和 [1, 10] = {}", ft.range_query(1, 10));
    }

    /// 示例2: 频率统计
    pub fn example_frequency_count() {
        println!("\n=== 频率统计示例 ===");

        let data = vec![3, 1, 4, 1, 5, 9, 2, 6, 5, 3];
        let max_val = *data.iter().max().unwrap() as usize;

        let mut ft = FenwickTree::new(max_val);

        // 统计每个数的出现频率
        for &val in &data {
            ft.update(val as usize, 1);
        }

        println!("数据: {:?}", data);
        println!("数字1出现次数: {}", ft.get(1));
        println!("数字3出现次数: {}", ft.get(3));
        println!("数字5出现次数: {}", ft.get(5));

        // 查询小于等于5的数字个数
        println!("小于等于5的数字个数: {}", ft.query(5));

        // 查询在[3, 7]范围内的数字个数
        println!("在[3, 7]范围内的数字个数: {}", ft.range_query(3, 7));
    }

    /// 示例3: 逆序对计数
    pub fn example_inversion_count() {
        println!("\n=== 逆序对计数示例 ===");

        let arr = vec![8, 4, 2, 1];
        let inversions = count_inversions(&arr);

        println!("数组: {:?}", arr);
        println!("逆序对数量: {}", inversions);
        println!("\n逆序对详情:");
        for i in 0..arr.len() {
            for j in (i + 1)..arr.len() {
                if arr[i] > arr[j] {
                    println!("  ({}, {}) -> ({}, {})", i, j, arr[i], arr[j]);
                }
            }
        }

        // 另一个例子
        let arr2 = vec![1, 20, 6, 4, 5];
        let inversions2 = count_inversions(&arr2);
        println!("\n数组 {:?} 的逆序对数量: {}", arr2, inversions2);
    }

    /// 示例4: 区间更新
    pub fn example_range_update() {
        println!("\n=== 区间更新示例 ===");

        let mut ft = RangeUpdateFenwickTree::new(10);

        // 初始: [0, 0, 0, 0, 0, 0, 0, 0, 0, 0]
        println!("初始数组: [0; 10]");

        ft.range_add(1, 5, 3);
        println!("range_add(1, 5, 3) -> 位置1-5增加3");

        ft.range_add(3, 8, 2);
        println!("range_add(3, 8, 2) -> 位置3-8增加2");

        ft.range_add(6, 10, 5);
        println!("range_add(6, 10, 5) -> 位置6-10增加5");

        // 结果应该是: [3, 3, 5, 5, 5, 7, 7, 7, 5, 5]
        println!("\n最终数组状态:");
        for i in 1..=10 {
            print!("{} ", ft.point_query(i));
        }
        println!();

        println!("区间和 [1, 5] = {}", ft.range_query(1, 5));
        println!("区间和 [6, 10] = {}", ft.range_query(6, 10));
    }

    /// 示例5: 第k小数查找
    pub fn example_kth_element() {
        println!("\n=== 第k小数查找示例 ===");

        let mut ft = FenwickTree::new(100);

        // 插入一些数据
        let data = vec![10, 20, 30, 40, 50, 20, 30, 10, 10];
        for &val in &data {
            ft.update(val, 1);
        }

        println!("数据: {:?}", data);
        println!("总元素数: {}", ft.query(100));

        // 查找第k小的数
        for k in [1, 3, 5, 7, 9] {
            if let Some(idx) = ft.find_kth(k) {
                println!("第{}小的数是: {}", k, idx);
            }
        }
    }
}
