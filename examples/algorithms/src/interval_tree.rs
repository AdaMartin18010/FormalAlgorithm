//! 区间树实现
//!
//! 区间树是一种增强的红黑树（或AVL树），用于高效存储区间并支持区间查询。
//! 每个节点存储一个区间和子树中所有区间的最大右端点，使得可以在 O(log n) 时间内
//! 找到与给定区间重叠的所有区间。
//!
//! # 算法特性
//! - 存储区间 [low, high]
//! - 每个节点维护子树中最大的 high 值
//! - 支持快速查找重叠区间
//! - 支持区间插入和删除
//!
//! # 时间复杂度
//! - 插入: O(log n)
//! - 删除: O(log n)
//! - 查找单个重叠区间: O(log n)
//! - 查找所有重叠区间: O(k log n)，k是重叠区间数量
//! - 空间: O(n)
//!
//! # 应用场景
//! - 日程安排系统
//! - 资源分配
//! - 基因组学（基因区间分析）
//! - 地理信息系统（范围查询）

use std::cmp::Ordering;
use std::fmt::{Debug, Display, Formatter, Result as FmtResult};
use std::ops::Range;

/// 区间类型
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub struct Interval<T: Ord + Clone + Copy> {
    pub low: T,
    pub high: T,
}

impl<T: Ord + Clone + Copy> Interval<T> {
    /// 创建新区间
    pub fn new(low: T, high: T) -> Self {
        assert!(low <= high, "Low must be <= high");
        Interval { low, high }
    }

    /// 检查是否与另一个区间重叠
    pub fn overlaps(&self, other: &Interval<T>) -> bool {
        self.low <= other.high && other.low <= self.high
    }

    /// 检查是否包含某一点
    pub fn contains(&self, point: T) -> bool {
        self.low <= point && point <= self.high
    }

    /// 区间长度
    pub fn length(&self) -> T
    where
        T: std::ops::Sub<Output = T> + From<u8>,
    {
        self.high - self.low
    }

    /// 转换为Range
    pub fn to_range(&self) -> Range<T> {
        self.low..self.high
    }
}

impl<T: Ord + Clone + Copy> From<Range<T>> for Interval<T> {
    fn from(range: Range<T>) -> Self {
        Interval::new(range.start, range.end)
    }
}

impl<T: Ord + Clone + Copy + Display> Display for Interval<T> {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        write!(f, "[{}, {}]", self.low, self.high)
    }
}

/// 区间树节点
#[derive(Debug)]
pub struct Node<T: Ord + Clone + Copy> {
    /// 区间
    interval: Interval<T>,
    /// 子树中最大的 high 值
    max_high: T,
    /// 左子树
    left: Option<Box<Node<T>>>,
    /// 右子树
    right: Option<Box<Node<T>>>,
    /// 节点高度（用于AVL平衡）
    height: i32,
}

impl<T: Ord + Clone + Copy> Node<T> {
    fn new(interval: Interval<T>) -> Self {
        let max_high = interval.high;
        Node {
            interval,
            max_high,
            left: None,
            right: None,
            height: 1,
        }
    }

    fn height(node: &Option<Box<Node<T>>>) -> i32 {
        node.as_ref().map_or(0, |n| n.height)
    }

    fn update_height(&mut self) {
        self.height = 1 + std::cmp::max(Self::height(&self.left), Self::height(&self.right));
    }

    fn update_max_high(&mut self) {
        self.max_high = self.interval.high;
        if let Some(ref left) = self.left {
            if left.max_high > self.max_high {
                self.max_high = left.max_high;
            }
        }
        if let Some(ref right) = self.right {
            if right.max_high > self.max_high {
                self.max_high = right.max_high;
            }
        }
    }

    fn balance_factor(&self) -> i32 {
        Self::height(&self.left) - Self::height(&self.right)
    }
}

/// 区间树
#[derive(Debug)]
pub struct IntervalTree<T: Ord + Clone + Copy + Debug> {
    root: Option<Box<Node<T>>>,
    size: usize,
}

impl<T: Ord + Clone + Copy + Debug> IntervalTree<T> {
    /// 创建空区间树
    pub fn new() -> Self {
        IntervalTree { root: None, size: 0 }
    }

    /// 获取元素数量
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 插入区间
    ///
    /// # 示例
    /// ```
    /// let mut tree = IntervalTree::new();
    /// tree.insert(Interval::new(1, 5));
    /// tree.insert(Interval::new(3, 7));
    /// ```
    pub fn insert(&mut self, interval: Interval<T>) {
        self.root = Self::insert_recursive(self.root.take(), interval);
        self.size += 1;
    }

    fn insert_recursive(node: Option<Box<Node<T>>>, interval: Interval<T>) -> Option<Box<Node<T>>> {
        let mut node = match node {
            None => return Some(Box::new(Node::new(interval))),
            Some(n) => n,
        };

        // 按 low 值进行BST插入
        match interval.low.cmp(&node.interval.low) {
            Ordering::Less => {
                node.left = Self::insert_recursive(node.left.take(), interval);
            }
            _ => {
                node.right = Self::insert_recursive(node.right.take(), interval);
            }
        }

        // 更新高度和max_high
        node.update_height();
        node.update_max_high();

        // 平衡树
        let balance = node.balance_factor();

        // 左左情况
        if balance > 1 && interval.low < node.left.as_ref().unwrap().interval.low {
            return Some(Self::rotate_right(node));
        }

        // 右右情况
        if balance < -1 && interval.low > node.right.as_ref().unwrap().interval.low {
            return Some(Self::rotate_left(node));
        }

        // 左右情况
        if balance > 1 && interval.low > node.left.as_ref().unwrap().interval.low {
            node.left = Some(Self::rotate_left(node.left.take().unwrap()));
            return Some(Self::rotate_right(node));
        }

        // 右左情况
        if balance < -1 && interval.low < node.right.as_ref().unwrap().interval.low {
            node.right = Some(Self::rotate_right(node.right.take().unwrap()));
            return Some(Self::rotate_left(node));
        }

        Some(node)
    }

    fn rotate_right(mut y: Box<Node<T>>) -> Box<Node<T>> {
        let mut x = y.left.take().unwrap();
        let t2 = x.right.take();

        x.right = Some(y);
        x.right.as_mut().unwrap().left = t2;

        x.right.as_mut().unwrap().update_height();
        x.right.as_mut().unwrap().update_max_high();
        x.update_height();
        x.update_max_high();

        x
    }

    fn rotate_left(mut x: Box<Node<T>>) -> Box<Node<T>> {
        let mut y = x.right.take().unwrap();
        let t2 = y.left.take();

        y.left = Some(x);
        y.left.as_mut().unwrap().right = t2;

        y.left.as_mut().unwrap().update_height();
        y.left.as_mut().unwrap().update_max_high();
        y.update_height();
        y.update_max_high();

        y
    }

    /// 查找与给定区间重叠的所有区间
    pub fn find_overlapping(&self, interval: &Interval<T>) -> Vec<Interval<T>> {
        let mut result = Vec::new();
        Self::find_overlapping_recursive(&self.root, interval, &mut result);
        result
    }

    fn find_overlapping_recursive(
        node: &Option<Box<Node<T>>>,
        interval: &Interval<T>,
        result: &mut Vec<Interval<T>>,
    ) {
        if let Some(n) = node {
            // 如果当前节点区间重叠，加入结果
            if n.interval.overlaps(interval) {
                result.push(n.interval);
            }

            // 剪枝：如果左子树可能存在重叠区间，搜索左子树
            if let Some(ref left) = n.left {
                if left.max_high >= interval.low {
                    Self::find_overlapping_recursive(&n.left, interval, result);
                }
            }

            // 搜索右子树（右子树的low一定大于当前节点的low）
            if n.interval.low <= interval.high {
                Self::find_overlapping_recursive(&n.right, interval, result);
            }
        }
    }

    /// 查找包含某点的所有区间
    pub fn find_containing_point(&self, point: T) -> Vec<Interval<T>> {
        let mut result = Vec::new();
        Self::find_containing_point_recursive(&self.root, point, &mut result);
        result
    }

    fn find_containing_point_recursive(
        node: &Option<Box<Node<T>>>,
        point: T,
        result: &mut Vec<Interval<T>>,
    ) {
        if let Some(n) = node {
            // 如果当前区间包含该点，加入结果
            if n.interval.contains(point) {
                result.push(n.interval);
            }

            // 剪枝搜索
            if let Some(ref left) = n.left {
                if left.max_high >= point {
                    Self::find_containing_point_recursive(&n.left, point, result);
                }
            }

            if n.interval.low <= point {
                Self::find_containing_point_recursive(&n.right, point, result);
            }
        }
    }

    /// 查找任意一个重叠区间
    pub fn find_any_overlapping(&self, interval: &Interval<T>) -> Option<Interval<T>> {
        Self::find_any_overlapping_recursive(&self.root, interval)
    }

    fn find_any_overlapping_recursive(
        node: &Option<Box<Node<T>>>,
        interval: &Interval<T>,
    ) -> Option<Interval<T>> {
        if let Some(n) = node {
            // 检查当前节点
            if n.interval.overlaps(interval) {
                return Some(n.interval);
            }

            // 如果左子树可能有重叠，先搜索左子树
            if let Some(ref left) = n.left {
                if left.max_high >= interval.low {
                    let result = Self::find_any_overlapping_recursive(&n.left, interval);
                    if result.is_some() {
                        return result;
                    }
                }
            }

            // 搜索右子树
            if n.interval.low <= interval.high {
                return Self::find_any_overlapping_recursive(&n.right, interval);
            }
        }
        None
    }

    /// 删除区间
    pub fn remove(&mut self, interval: &Interval<T>) -> bool {
        let (new_root, removed) = Self::remove_recursive(self.root.take(), interval);
        self.root = new_root;
        if removed {
            self.size -= 1;
        }
        removed
    }

    fn remove_recursive(
        node: Option<Box<Node<T>>>,
        interval: &Interval<T>,
    ) -> (Option<Box<Node<T>>>, bool) {
        let mut node = match node {
            None => return (None, false),
            Some(n) => n,
        };

        let mut removed = false;

        // 比较区间
        match interval.low.cmp(&node.interval.low) {
            Ordering::Less => {
                let (new_left, r) = Self::remove_recursive(node.left.take(), interval);
                node.left = new_left;
                removed = r;
            }
            Ordering::Greater => {
                let (new_right, r) = Self::remove_recursive(node.right.take(), interval);
                node.right = new_right;
                removed = r;
            }
            Ordering::Equal => {
                if interval.high == node.interval.high {
                    // 找到要删除的节点
                    removed = true;

                    if node.left.is_none() {
                        return (node.right, true);
                    } else if node.right.is_none() {
                        return (node.left, true);
                    } else {
                        // 有两个子节点，找到后继
                        let (succ, new_right) = Self::extract_min(node.right.take().unwrap());
                        let mut succ = succ.unwrap();
                        succ.left = node.left;
                        succ.right = new_right;
                        succ.update_height();
                        succ.update_max_high();
                        return (Some(succ), true);
                    }
                } else {
                    let (new_right, r) = Self::remove_recursive(node.right.take(), interval);
                    node.right = new_right;
                    removed = r;
                }
            }
        }

        if removed {
            node.update_height();
            node.update_max_high();
        }

        (Some(node), removed)
    }

    fn extract_min(mut node: Box<Node<T>>) -> (Option<Box<Node<T>>>, Option<Box<Node<T>>>) {
        if node.left.is_none() {
            return (Some(node), None);
        }

        let (min, new_left) = Self::extract_min(node.left.take().unwrap());
        node.left = new_left;
        node.update_height();
        node.update_max_high();

        (min, Some(node))
    }

    /// 获取树的高度
    pub fn height(&self) -> i32 {
        Node::height(&self.root)
    }

    /// 中序遍历获取所有区间
    pub fn inorder_traversal(&self) -> Vec<Interval<T>> {
        let mut result = Vec::new();
        Self::inorder_recursive(&self.root, &mut result);
        result
    }

    fn inorder_recursive(node: &Option<Box<Node<T>>>, result: &mut Vec<Interval<T>>) {
        if let Some(n) = node {
            Self::inorder_recursive(&n.left, result);
            result.push(n.interval);
            Self::inorder_recursive(&n.right, result);
        }
    }

    /// 检查区间是否存在
    pub fn contains(&self, interval: &Interval<T>) -> bool {
        Self::contains_recursive(&self.root, interval)
    }

    fn contains_recursive(node: &Option<Box<Node<T>>>, interval: &Interval<T>) -> bool {
        match node {
            None => false,
            Some(n) => {
                if n.interval == *interval {
                    return true;
                }
                match interval.low.cmp(&n.interval.low) {
                    Ordering::Less => Self::contains_recursive(&n.left, interval),
                    _ => Self::contains_recursive(&n.right, interval),
                }
            }
        }
    }
}

impl<T: Ord + Clone + Copy + Debug> Default for IntervalTree<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 区间集合操作
pub struct IntervalSet<T: Ord + Clone + Copy + Debug>(std::marker::PhantomData<T>);

impl<T: Ord + Clone + Copy + Debug> IntervalSet<T> {
    /// 创建新区间集合
    pub fn new() -> Self {
        Self(std::marker::PhantomData)
    }

    /// 合并重叠区间
    pub fn merge_intervals(mut intervals: Vec<Interval<T>>) -> Vec<Interval<T>> {
        if intervals.len() <= 1 {
            return intervals;
        }

        // 按起点排序
        intervals.sort_by_key(|i| i.low);

        let mut merged = Vec::new();
        let mut current = intervals[0];

        for interval in intervals.iter().skip(1) {
            if interval.low <= current.high {
                // 重叠，扩展当前区间
                if interval.high > current.high {
                    current.high = interval.high;
                }
            } else {
                // 不重叠，保存当前区间
                merged.push(current);
                current = *interval;
            }
        }
        merged.push(current);

        merged
    }

    /// 计算区间并集
    pub fn union(intervals1: &[Interval<T>], intervals2: &[Interval<T>]) -> Vec<Interval<T>> {
        let mut all = intervals1.to_vec();
        all.extend_from_slice(intervals2);
        Self::merge_intervals(all)
    }

    /// 计算区间交集
    pub fn intersection(intervals1: &[Interval<T>], intervals2: &[Interval<T>]) -> Vec<Interval<T>> {
        let mut result = Vec::new();

        for i1 in intervals1 {
            for i2 in intervals2 {
                if i1.overlaps(i2) {
                    result.push(Interval::new(
                        std::cmp::max(i1.low, i2.low),
                        std::cmp::min(i1.high, i2.high),
                    ));
                }
            }
        }

        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree: IntervalTree<i32> = IntervalTree::new();
        assert!(tree.is_empty());
        assert_eq!(tree.len(), 0);
    }

    #[test]
    fn test_insert_and_find() {
        let mut tree = IntervalTree::new();
        tree.insert(Interval::new(1, 5));
        tree.insert(Interval::new(3, 7));
        tree.insert(Interval::new(8, 10));

        assert_eq!(tree.len(), 3);

        // 查找与 [4, 6] 重叠的区间
        let overlapping = tree.find_overlapping(&Interval::new(4, 6));
        assert_eq!(overlapping.len(), 2);
    }

    #[test]
    fn test_no_overlap() {
        let mut tree = IntervalTree::new();
        tree.insert(Interval::new(1, 3));
        tree.insert(Interval::new(5, 7));

        let overlapping = tree.find_overlapping(&Interval::new(10, 15));
        assert!(overlapping.is_empty());
    }

    #[test]
    fn test_point_query() {
        let mut tree = IntervalTree::new();
        tree.insert(Interval::new(1, 5));
        tree.insert(Interval::new(3, 7));
        tree.insert(Interval::new(10, 15));

        let containing_4 = tree.find_containing_point(4);
        assert_eq!(containing_4.len(), 2);

        let containing_20 = tree.find_containing_point(20);
        assert!(containing_20.is_empty());
    }

    #[test]
    fn test_remove() {
        let mut tree = IntervalTree::new();
        tree.insert(Interval::new(1, 5));
        tree.insert(Interval::new(3, 7));

        assert!(tree.remove(&Interval::new(1, 5)));
        assert_eq!(tree.len(), 1);
        assert!(!tree.contains(&Interval::new(1, 5)));
        assert!(tree.contains(&Interval::new(3, 7)));
    }

    #[test]
    fn test_interval_overlaps() {
        let i1 = Interval::new(1, 5);
        let i2 = Interval::new(3, 7);
        let i3 = Interval::new(6, 10);

        assert!(i1.overlaps(&i2));
        assert!(i2.overlaps(&i1));
        assert!(!i1.overlaps(&i3));
    }

    #[test]
    fn test_merge_intervals() {
        let intervals = vec![
            Interval::new(1, 3),
            Interval::new(2, 6),
            Interval::new(8, 10),
            Interval::new(15, 18),
        ];

        let merged = IntervalSet::merge_intervals(intervals);
        assert_eq!(merged.len(), 3);
        assert_eq!(merged[0], Interval::new(1, 6));
        assert_eq!(merged[1], Interval::new(8, 10));
        assert_eq!(merged[2], Interval::new(15, 18));
    }

    #[test]
    fn test_intersection() {
        let i1 = vec![Interval::new(1, 5), Interval::new(10, 15)];
        let i2 = vec![Interval::new(3, 7), Interval::new(12, 20)];

        let intersection = IntervalSet::intersection(&i1, &i2);
        assert_eq!(intersection.len(), 2);
        assert!(intersection.contains(&Interval::new(3, 5)));
        assert!(intersection.contains(&Interval::new(12, 15)));
    }

    #[test]
    fn test_large_tree() {
        let mut tree = IntervalTree::new();

        // 插入大量区间
        for i in 0..100 {
            tree.insert(Interval::new(i * 2, i * 2 + 5));
        }

        assert_eq!(tree.len(), 100);

        // 查询应该保持高效
        let overlapping = tree.find_overlapping(&Interval::new(50, 60));
        assert!(!overlapping.is_empty());
    }

    #[test]
    fn test_from_range() {
        let interval: Interval<i32> = (1..10).into();
        assert_eq!(interval.low, 1);
        assert_eq!(interval.high, 10);
    }

    #[test]
    fn test_find_any_overlapping() {
        let mut tree = IntervalTree::new();
        tree.insert(Interval::new(1, 5));
        tree.insert(Interval::new(10, 20));

        let any = tree.find_any_overlapping(&Interval::new(3, 7));
        assert!(any.is_some());
        assert_eq!(any.unwrap(), Interval::new(1, 5));

        let none = tree.find_any_overlapping(&Interval::new(100, 200));
        assert!(none.is_none());
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn scheduling_example() {
        println!("\n=== Meeting Room Scheduling ===");

        let mut schedule = IntervalTree::new();

        // 添加会议
        let meetings = vec![
            ("Team Standup", Interval::new(9, 10)),
            ("Product Review", Interval::new(10, 11)),
            ("Client Meeting", Interval::new(14, 16)),
            ("Code Review", Interval::new(9, 10)),
            ("Sprint Planning", Interval::new(13, 15)),
        ];

        for (name, interval) in meetings {
            schedule.insert(interval);
            println!("Scheduled: {} at {:?}", name, interval);
        }

        // 查询下午2点的会议
        println!("\nMeetings at 14:00:");
        let at_2pm = schedule.find_containing_point(14);
        for interval in at_2pm {
            println!("  {:?}", interval);
        }

        // 查询与15:00-16:00冲突的会议
        println!("\nMeetings overlapping with 15:00-16:00:");
        let overlapping = schedule.find_overlapping(&Interval::new(15, 16));
        for interval in overlapping {
            println!("  {:?}", interval);
        }
    }

    #[test]
    fn genome_analysis_example() {
        println!("\n=== Genome Interval Analysis ===");

        let mut gene_tree = IntervalTree::new();

        // 模拟基因区间
        let genes = vec![
            Interval::new(1000, 5000),   // Gene A
            Interval::new(3000, 7000),   // Gene B (overlaps A)
            Interval::new(8000, 12000),  // Gene C
            Interval::new(15000, 20000), // Gene D
        ];

        for gene in &genes {
            gene_tree.insert(*gene);
        }

        // 查询与变异位点重叠的基因
        let mutation = Interval::new(2500, 3500);
        println!("Mutation at {:?}", mutation);
        println!("Overlapping genes:");

        let affected = gene_tree.find_overlapping(&mutation);
        for gene in affected {
            println!("  Gene at {:?}", gene);
        }
    }

    #[test]
    fn resource_allocation_example() {
        println!("\n=== Resource Allocation ===");

        let mut allocations = IntervalTree::new();

        // 模拟资源占用时间
        let reservations = vec![
            ("Server A", Interval::new(0, 4)),
            ("Server B", Interval::new(3, 7)),
            ("Server C", Interval::new(8, 12)),
            ("Server D", Interval::new(5, 10)),
        ];

        for (server, interval) in reservations {
            allocations.insert(interval);
            println!("{} reserved: {:?}", server, interval);
        }

        // 查找空闲时间段
        println!("\nChecking availability for 2-hour slots:");
        for start in 0..12 {
            let query = Interval::new(start, start + 2);
            let overlapping = allocations.find_overlapping(&query);
            if overlapping.is_empty() {
                println!("  Available: {:?}", query);
            }
        }
    }

    #[test]
    fn tree_visualization() {
        println!("\n=== Interval Tree Structure ===");

        let mut tree = IntervalTree::new();
        let intervals = vec![
            Interval::new(15, 20),
            Interval::new(10, 30),
            Interval::new(17, 19),
            Interval::new(5, 20),
            Interval::new(12, 15),
        ];

        for interval in intervals {
            tree.insert(interval);
        }

        println!("Inorder traversal:");
        for interval in tree.inorder_traversal() {
            println!("  {:?}", interval);
        }

        println!("\nTree height: {}", tree.height());
        println!("Total intervals: {}", tree.len());
    }
}
