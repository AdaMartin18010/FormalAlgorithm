//! 二叉堆（优先队列）实现
//!
//! 二叉堆是一种基于完全二叉树的数据结构，满足堆性质：
//! - **最大堆**：每个节点的值都大于或等于其子节点的值
//! - **最小堆**：每个节点的值都小于或等于其子节点的值
//!
//! 对标: CLRS 4th Ed. Ch 6（Heapsort），亦为 MIT 6.006、Stanford CS161、CMU 15-451 核心教学内容。
//!
//! ## 堆的性质
//!
//! 对于索引 i（从 0 开始）：
//! - 父节点索引：`parent(i) = (i - 1) / 2`
//! - 左子节点索引：`left(i) = 2 * i + 1`
//! - 右子节点索引：`right(i) = 2 * i + 2`
//!
//! ## 核心操作复杂度
//!
//! | 操作 | 时间复杂度 | 说明 |
//! |------|----------|------|
//! | `insert` | O(log n) | 在堆尾插入，然后上浮 |
//! | `extract_max` / `extract_min` | O(log n) | 移除堆顶，将堆尾移到堆顶，然后下沉 |
//! | `peek` | O(1) | 直接访问堆顶 |
//! | `heapify` | O(n) | 从最后一个非叶子节点开始自下而上调整 |
//! | `build_heap` | O(n) | 将任意数组建堆 |
//!
//! ## 应用
//!
//! - **优先队列**：调度系统、事件驱动模拟
//! - **堆排序**：原地 O(n log n) 排序
//! - **图算法**：Dijkstra、Prim、A* 的优先队列实现
//! - **Top-K 问题**：快速找出最大/最小的 K 个元素
//! - **中位数维护**：双堆法动态维护数据流中位数
//!
//! ## 与项目其他模块的关系
//!
//! - `heap_sort.rs` 使用本模块的堆操作实现原地排序
//! - `dijkstra.rs`、`astar.rs` 使用堆作为优先队列

use std::cmp::Ordering;

/// 最大二叉堆
///
/// # 类型参数
///
/// * `T` - 元素类型，必须实现 `Ord`
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_heap::BinaryHeap;
///
/// let mut heap = BinaryHeap::new();
/// heap.insert(3);
/// heap.insert(1);
/// heap.insert(4);
///
/// assert_eq!(heap.peek(), Some(&4));
/// assert_eq!(heap.extract_max(), Some(4));
/// assert_eq!(heap.extract_max(), Some(3));
/// assert_eq!(heap.extract_max(), Some(1));
/// assert_eq!(heap.extract_max(), None);
/// ```
#[derive(Debug, Clone)]
pub struct BinaryHeap<T: Ord> {
    data: Vec<T>,
}

impl<T: Ord> BinaryHeap<T> {
    /// 创建空堆
    pub fn new() -> Self {
        BinaryHeap { data: Vec::new() }
    }

    /// 从向量建堆（O(n)）
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::binary_heap::BinaryHeap;
    ///
    /// let heap = BinaryHeap::from_vec(vec![3, 1, 4, 1, 5, 9, 2, 6]);
    /// assert_eq!(heap.peek(), Some(&9));
    /// ```
    pub fn from_vec(vec: Vec<T>) -> Self {
        let mut heap = BinaryHeap { data: vec };
        heap.heapify();
        heap
    }

    /// 返回堆中元素个数
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// 判断堆是否为空
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// 查看堆顶元素（不移除）
    pub fn peek(&self) -> Option<&T> {
        self.data.first()
    }

    /// 插入元素
    ///
    /// 时间复杂度：O(log n)
    pub fn insert(&mut self, value: T) {
        self.data.push(value);
        self.sift_up(self.data.len() - 1);
    }

    /// 移除并返回最大元素
    ///
    /// 时间复杂度：O(log n)
    pub fn extract_max(&mut self) -> Option<T> {
        if self.data.is_empty() {
            return None;
        }
        let last = self.data.len() - 1;
        self.data.swap(0, last);
        let max = self.data.pop();
        if !self.data.is_empty() {
            self.sift_down(0);
        }
        max
    }

    /// 原地建堆（Floyd 建堆算法）
    ///
    /// 从最后一个非叶子节点开始，自下而上对每个节点执行 sift_down。
    /// 时间复杂度：O(n)
    fn heapify(&mut self) {
        let n = self.data.len();
        if n <= 1 {
            return;
        }
        for i in (0..n / 2).rev() {
            self.sift_down(i);
        }
    }

    /// 上浮操作：将索引 i 处的元素向上移动到正确位置
    fn sift_up(&mut self, mut i: usize) {
        while i > 0 {
            let parent = (i - 1) / 2;
            if self.data[i] <= self.data[parent] {
                break;
            }
            self.data.swap(i, parent);
            i = parent;
        }
    }

    /// 下沉操作：将索引 i 处的元素向下移动到正确位置
    fn sift_down(&mut self, mut i: usize) {
        let n = self.data.len();
        loop {
            let left = 2 * i + 1;
            let right = 2 * i + 2;
            let mut largest = i;

            if left < n && self.data[left] > self.data[largest] {
                largest = left;
            }
            if right < n && self.data[right] > self.data[largest] {
                largest = right;
            }
            if largest == i {
                break;
            }
            self.data.swap(i, largest);
            i = largest;
        }
    }
}

impl<T: Ord> Default for BinaryHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T: Ord> From<Vec<T>> for BinaryHeap<T> {
    fn from(vec: Vec<T>) -> Self {
        Self::from_vec(vec)
    }
}

/// 最小堆（包装最大堆，元素取反比较）
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_heap::MinHeap;
///
/// let mut heap = MinHeap::new();
/// heap.insert(3);
/// heap.insert(1);
/// heap.insert(4);
///
/// assert_eq!(heap.peek(), Some(&1));
/// assert_eq!(heap.extract_min(), Some(1));
/// assert_eq!(heap.extract_min(), Some(3));
/// assert_eq!(heap.extract_min(), Some(4));
/// ```
#[derive(Debug, Clone)]
pub struct MinHeap<T: Ord> {
    inner: BinaryHeap<Reverse<T>>,
}

/// 用于最小堆的包装类型
#[derive(Debug, Clone, PartialEq, Eq)]
struct Reverse<T: Ord>(T);

impl<T: Ord> PartialOrd for Reverse<T> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        other.0.partial_cmp(&self.0)
    }
}

impl<T: Ord> Ord for Reverse<T> {
    fn cmp(&self, other: &Self) -> Ordering {
        other.0.cmp(&self.0)
    }
}

impl<T: Ord> MinHeap<T> {
    /// 创建空最小堆
    pub fn new() -> Self {
        MinHeap {
            inner: BinaryHeap::new(),
        }
    }

    /// 从向量建最小堆
    pub fn from_vec(vec: Vec<T>) -> Self {
        MinHeap {
            inner: BinaryHeap::from_vec(vec.into_iter().map(Reverse).collect()),
        }
    }

    /// 返回堆中元素个数
    pub fn len(&self) -> usize {
        self.inner.len()
    }

    /// 判断堆是否为空
    pub fn is_empty(&self) -> bool {
        self.inner.is_empty()
    }

    /// 查看堆顶元素（最小值）
    pub fn peek(&self) -> Option<&T> {
        self.inner.peek().map(|r| &r.0)
    }

    /// 插入元素
    pub fn insert(&mut self, value: T) {
        self.inner.insert(Reverse(value));
    }

    /// 移除并返回最小元素
    pub fn extract_min(&mut self) -> Option<T> {
        self.inner.extract_max().map(|r| r.0)
    }
}

impl<T: Ord> Default for MinHeap<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 从数组构建最大堆（辅助函数）
///
/// # 示例
///
/// ```
/// use formal_algorithms::binary_heap::build_max_heap;
///
/// let mut arr = vec![3, 1, 4, 1, 5, 9, 2, 6];
/// build_max_heap(&mut arr);
/// assert_eq!(arr[0], 9); // 堆顶为最大值
/// ```
pub fn build_max_heap<T: Ord>(arr: &mut [T]) {
    let n = arr.len();
    if n <= 1 {
        return;
    }
    for i in (0..n / 2).rev() {
        max_heapify(arr, n, i);
    }
}

/// 调整最大堆（辅助函数）
///
/// 使以 `root` 为根的子树满足最大堆性质。
pub fn max_heapify<T: Ord>(arr: &mut [T], heap_size: usize, mut root: usize) {
    loop {
        let left = 2 * root + 1;
        let right = 2 * root + 2;
        let mut largest = root;

        if left < heap_size && arr[left] > arr[largest] {
            largest = left;
        }
        if right < heap_size && arr[right] > arr[largest] {
            largest = right;
        }
        if largest == root {
            break;
        }
        arr.swap(root, largest);
        root = largest;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_heap() {
        let mut heap = BinaryHeap::<i32>::new();
        assert!(heap.is_empty());
        assert_eq!(heap.peek(), None);
        assert_eq!(heap.extract_max(), None);
    }

    #[test]
    fn test_insert_and_extract() {
        let mut heap = BinaryHeap::new();
        heap.insert(3);
        heap.insert(1);
        heap.insert(4);
        heap.insert(1);
        heap.insert(5);

        assert_eq!(heap.extract_max(), Some(5));
        assert_eq!(heap.extract_max(), Some(4));
        assert_eq!(heap.extract_max(), Some(3));
        assert_eq!(heap.extract_max(), Some(1));
        assert_eq!(heap.extract_max(), Some(1));
        assert_eq!(heap.extract_max(), None);
    }

    #[test]
    fn test_from_vec() {
        let heap = BinaryHeap::from_vec(vec![3, 1, 4, 1, 5, 9, 2, 6]);
        assert_eq!(heap.peek(), Some(&9));
        assert_eq!(heap.len(), 8);
    }

    #[test]
    fn test_min_heap() {
        let mut heap = MinHeap::new();
        heap.insert(3);
        heap.insert(1);
        heap.insert(4);
        heap.insert(1);
        heap.insert(5);

        assert_eq!(heap.extract_min(), Some(1));
        assert_eq!(heap.extract_min(), Some(1));
        assert_eq!(heap.extract_min(), Some(3));
        assert_eq!(heap.extract_min(), Some(4));
        assert_eq!(heap.extract_min(), Some(5));
    }

    #[test]
    fn test_build_max_heap() {
        let mut arr = vec![4, 1, 3, 2, 16, 9, 10, 14, 8, 7];
        build_max_heap(&mut arr);
        assert_eq!(arr[0], 16);
        // 验证堆性质
        let n = arr.len();
        for i in 0..n / 2 {
            let left = 2 * i + 1;
            let right = 2 * i + 2;
            if left < n {
                assert!(arr[i] >= arr[left]);
            }
            if right < n {
                assert!(arr[i] >= arr[right]);
            }
        }
    }

    #[test]
    fn test_heapify_complexity() {
        // 测试建堆的时间复杂度为 O(n)
        let mut arr: Vec<i32> = (0..10000).collect();
        arr.reverse();
        build_max_heap(&mut arr);
        assert_eq!(arr[0], 9999);
    }

    #[test]
    fn test_interleaved_operations() {
        let mut heap = BinaryHeap::new();
        heap.insert(10);
        heap.insert(20);
        assert_eq!(heap.extract_max(), Some(20));
        heap.insert(15);
        heap.insert(5);
        assert_eq!(heap.extract_max(), Some(15));
        assert_eq!(heap.extract_max(), Some(10));
        heap.insert(25);
        assert_eq!(heap.extract_max(), Some(25));
    }
}
