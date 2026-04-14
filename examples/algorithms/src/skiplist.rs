//! # 跳表 (Skip List)
//!
//! ## 算法描述
//! 跳表是一种概率性的数据结构，通过在多层链表上建立索引，实现类似平衡树的搜索效率。
//!
//! ## 核心思想
//! - 最底层是完整的有序链表
//! - 每个元素以概率 p（通常 0.5）向上层提升
//! - 上层链表是下层链表的"快速通道"
//! - 搜索时从顶层开始，快速跳过不可能包含目标的区间
//!
//! ## 为什么使用跳表？
//! - 实现简单，比红黑树/AVL树容易得多
//! - 插入、删除、查找都是 O(log n)
//! - 支持高效的范围查询
//! - 无锁实现相对容易（并发友好）
//!
//! ## 复杂度分析
//! | 操作 | 平均时间 | 最坏时间 | 空间复杂度 |
//! |------|---------|---------|-----------|
//! | 查找 | O(log n) | O(n) | O(n) |
//! | 插入 | O(log n) | O(n) | O(n) |
//! | 删除 | O(log n) | O(n) | O(n) |
//! | 范围查询 | O(log n + k) | O(n) | O(k) |
//!
//! 其中 k 是范围内元素数量

use rand::Rng;
use std::cmp::Ordering;

/// 默认最大层数
const MAX_LEVEL: usize = 32;
/// 默认提升概率
const P: f64 = 0.5;

/// 跳表节点
struct Node<T> {
    /// 存储的值
    value: Option<T>,
    /// 每一层的下一个节点
    /// forward[i] 表示第 i 层的下一个节点
    forward: Vec<Option<Box<Node<T>>>>,
}

impl<T> Node<T> {
    /// 创建新节点（头节点）
    fn new_head(level: usize) -> Self {
        let mut forward = Vec::with_capacity(level);
        for _ in 0..level {
            forward.push(None);
        }
        Self {
            value: None,
            forward,
        }
    }

    /// 创建新节点（数据节点）
    fn new(value: T, level: usize) -> Self {
        let mut forward = Vec::with_capacity(level);
        for _ in 0..level {
            forward.push(None);
        }
        Self {
            value: Some(value),
            forward,
        }
    }
}

/// 跳表结构
///
/// # 类型参数
/// - `T`: 元素类型，需要实现 Ord trait
///
/// # 示例
/// ```
/// use algorithms::skiplist::SkipList;
///
/// let mut list = SkipList::new();
/// list.insert(3);
/// list.insert(1);
/// list.insert(2);
///
/// assert!(list.contains(&2));
/// assert_eq!(list.len(), 3);
/// ```
pub struct SkipList<T: Ord> {
    /// 头节点，不存储实际数据
    head: Box<Node<T>>,
    /// 当前最大层数
    level: usize,
    /// 元素数量
    length: usize,
    /// 最大层数限制
    max_level: usize,
    /// 提升概率
    p: f64,
}

impl<T: Ord + Clone + std::fmt::Debug> SkipList<T> {
    /// 创建默认配置的跳表
    pub fn new() -> Self {
        Self::with_params(MAX_LEVEL, P)
    }

    /// 创建指定参数的跳表
    ///
    /// # 参数
    /// - `max_level`: 最大层数
    /// - `p`: 提升概率
    pub fn with_params(max_level: usize, p: f64) -> Self {
        // 创建一个虚拟的头节点
        let head = Box::new(Node::new_head(max_level));
        
        Self {
            head,
            level: 1,
            length: 0,
            max_level,
            p,
        }
    }

    /// 随机生成层数
    ///
    /// 使用几何分布，每层以概率 p 提升
    fn random_level(&self) -> usize {
        let mut level = 1;
        let mut rng = rand::thread_rng();
        
        while level < self.max_level && rng.gen::<f64>() < self.p {
            level += 1;
        }
        
        level
    }

    /// 搜索元素
    ///
    /// # 参数
    /// - `target`: 要搜索的值
    ///
    /// # 返回值
    /// - `true`: 元素存在
    /// - `false`: 元素不存在
    ///
    /// # 复杂度
    /// - 平均 O(log n)，最坏 O(n)
    pub fn contains(&self, target: &T) -> bool {
        let mut current = &self.head;
        
        // 从最高层开始搜索
        for i in (0..self.level).rev() {
            // 在当前层向右移动，直到下一个节点值 >= target
            while let Some(ref next) = (&current.forward)[i] {
                match next.value.as_ref().unwrap().cmp(target) {
                    Ordering::Less => {
                        current = next;
                    }
                    Ordering::Equal => {
                        return true;
                    }
                    Ordering::Greater => {
                        break;
                    }
                }
            }
        }
        
        false
    }

    /// 插入元素
    ///
    /// # 参数
    /// - `value`: 要插入的值
    ///
    /// # 说明
    /// - 如果元素已存在，不重复插入
    ///
    /// # 复杂度
    /// - 平均 O(log n)，最坏 O(n)
    pub fn insert(&mut self, value: T) {
        // 如果元素已存在，不插入
        if self.contains(&value) {
            return;
        }

        let mut update: Vec<*mut Node<T>> = vec![std::ptr::null_mut(); self.max_level];
        let mut current: *mut Node<T> = &mut *self.head;
        
        // 找到每一层需要更新的位置
        for i in (0..self.level).rev() {
            unsafe {
                while let Some(ref next) = (&(*current).forward)[i] {
                    if next.value.as_ref().unwrap() < &value {
                        current = &**next as *const _ as *mut _;
                    } else {
                        break;
                    }
                }
                update[i] = current;
            }
        }
        
        // 随机生成新节点的层数
        let new_level = self.random_level();
        
        // 如果新节点层数超过当前层数，更新头节点的 forward
        if new_level > self.level {
            for i in self.level..new_level {
                update[i] = &mut *self.head;
            }
            self.level = new_level;
        }
        
        // 创建新节点
        let new_node = Box::new(Node::new(value, new_level));
        let new_node_ptr = Box::into_raw(new_node);
        
        // 更新各层的指针
        unsafe {
            for i in 0..new_level {
                (&mut (*new_node_ptr).forward)[i] = (&mut (*update[i]).forward)[i].take();
                (&mut (*update[i]).forward)[i] = Some(Box::from_raw(new_node_ptr));
            }
        }
        
        self.length += 1;
    }

    /// 删除元素
    ///
    /// # 参数
    /// - `target`: 要删除的值
    ///
    /// # 返回值
    /// - `true`: 删除成功
    /// - `false`: 元素不存在
    ///
    /// # 复杂度
    /// - 平均 O(log n)，最坏 O(n)
    pub fn remove(&mut self, target: &T) -> bool {
        let mut update: Vec<*mut Node<T>> = vec![std::ptr::null_mut(); self.max_level];
        let mut current: *mut Node<T> = &mut *self.head;
        let mut found = false;
        
        // 找到每一层需要更新的位置
        for i in (0..self.level).rev() {
            unsafe {
                while let Some(ref next) = (&(*current).forward)[i] {
                    match next.value.as_ref().unwrap().cmp(target) {
                        Ordering::Less => {
                            current = &**next as *const _ as *mut _;
                        }
                        Ordering::Equal => {
                            found = true;
                            update[i] = current;
                            break;
                        }
                        Ordering::Greater => {
                            break;
                        }
                    }
                }
                if !found {
                    update[i] = current;
                }
            }
        }
        
        if !found {
            return false;
        }
        
        // 更新各层指针，跳过要删除的节点
        for i in 0..self.level {
            unsafe {
                if let Some(ref mut next) = (&mut (*update[i]).forward)[i] {
                    if next.value.as_ref().unwrap() == target {
                        (&mut (*update[i]).forward)[i] = next.forward[i].take();
                    }
                }
            }
        }
        
        // 更新当前最大层数
        while self.level > 1 && self.head.forward[self.level - 1].is_none() {
            self.level -= 1;
        }
        
        self.length -= 1;
        true
    }

    /// 获取范围内的所有元素
    ///
    /// # 参数
    /// - `start`: 范围起始（包含）
    /// - `end`: 范围结束（包含）
    ///
    /// # 返回值
    /// 范围内的元素向量
    ///
    /// # 复杂度
    /// - O(log n + k)，k 是范围内元素数量
    pub fn range(&self, start: &T, end: &T) -> Vec<&T> {
        let mut result = Vec::new();
        let mut current = &self.head;
        
        // 找到起始位置
        for i in (0..self.level).rev() {
            while let Some(ref next) = (&current.forward)[i] {
                if next.value.as_ref().unwrap() < start {
                    current = next;
                } else {
                    break;
                }
            }
        }
        
        // 收集范围内的元素
        current = if let Some(ref next) = current.forward[0] {
            next
        } else {
            return result;
        };
        
        while current.value.as_ref().unwrap() <= end {
            result.push(current.value.as_ref().unwrap());
            current = if let Some(ref next) = (&current.forward)[0] {
                next
            } else {
                break;
            };
        }
        
        result
    }

    /// 获取第 k 小的元素（0-indexed）
    ///
    /// # 复杂度
    /// - O(k)
    pub fn kth(&self, k: usize) -> Option<&T> {
        if k >= self.length {
            return None;
        }
        
        let mut current = &self.head;
        for _ in 0..=k {
            current = current.forward[0].as_ref()?;
        }
        
        Some(current.value.as_ref().unwrap())
    }

    /// 获取最小元素
    pub fn min(&self) -> Option<&T> {
        self.head.forward[0].as_ref().map(|node| node.value.as_ref().unwrap())
    }

    /// 获取最大元素
    pub fn max(&self) -> Option<&T> {
        let mut current: *const Node<T> = &*self.head;
        
        for i in (0..self.level).rev() {
            unsafe {
                while let Some(ref next) = (&(*current).forward)[i] {
                    current = &**next;
                }
            }
        }
        
        // 检查是否是头节点
        let head_ptr: *const Node<T> = &*self.head;
        
        if std::ptr::eq(current, head_ptr) {
            None
        } else {
            unsafe { Some((*current).value.as_ref().unwrap()) }
        }
    }

    /// 返回元素数量
    pub fn len(&self) -> usize {
        self.length
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.length == 0
    }

    /// 清空跳表
    pub fn clear(&mut self) {
        for i in 0..self.max_level {
            self.head.forward[i] = None;
        }
        self.level = 1;
        self.length = 0;
    }

    /// 遍历所有元素（升序）
    pub fn iter(&self) -> Vec<&T> {
        let mut result = Vec::new();
        let mut current = &self.head;
        
        while let Some(ref next) = current.forward[0] {
            result.push(next.value.as_ref().unwrap());
            current = next;
        }
        
        result
    }

    /// 获取当前层数
    pub fn level(&self) -> usize {
        self.level
    }
}

impl<T: Ord + Clone + std::fmt::Debug> Default for SkipList<T> {
    fn default() -> Self {
        Self::new()
    }
}

/// 打印跳表结构（用于调试）
pub fn print_skiplist_structure<T: Ord + Clone + std::fmt::Debug>(list: &SkipList<T>) {
    println!("SkipList Structure (level={}, length={}):", list.level, list.length);
    
    for i in (0..list.level).rev() {
        print!("Level {}: head", i);
        let mut current = &list.head;
        
        while let Some(ref next) = (&current.forward)[i] {
            print!(" -> {:?}", next.value.as_ref().unwrap());
            current = next;
        }
        println!(" -> null");
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut list = SkipList::new();
        
        list.insert(3);
        list.insert(1);
        list.insert(2);
        
        assert!(list.contains(&1));
        assert!(list.contains(&2));
        assert!(list.contains(&3));
        assert!(!list.contains(&4));
        
        assert_eq!(list.len(), 3);
    }

    #[test]
    fn test_min_max() {
        let mut list = SkipList::new();
        
        assert_eq!(list.min(), None);
        
        list.insert(5);
        list.insert(1);
        list.insert(10);
        
        assert_eq!(list.min(), Some(&1));
    }
}

/// 使用示例
///
/// ```
/// use algorithms::skiplist::SkipList;
///
/// fn main() {
///     let mut scores = SkipList::new();
///     
///     // 添加玩家分数
///     scores.insert(100);
///     scores.insert(85);
///     scores.insert(120);
///     scores.insert(95);
///     
///     // 查询分数是否存在
///     println!("是否有 100 分: {}", scores.contains(&100));
///     
///     // 获取排名（第几小）
///     println!("第 1 名分数: {:?}", scores.kth(0));
///     println!("第 2 名分数: {:?}", scores.kth(1));
///     
///     // 范围查询
///     println!("90-110 分之间的玩家:");
///     for score in scores.range(&90, &110) {
///         println!("  {}", score);
///     }
///     
///     // 遍历所有分数（升序）
///     println!("所有分数（升序）:");
///     for score in scores.iter() {
///         println!("  {}", score);
///     }
/// }
/// ```
pub fn example_usage() {
    let mut leaderboard: SkipList<(u32, String)> = SkipList::new();
    
    // 添加玩家数据（分数，名字）
    leaderboard.insert((1500, "Alice".to_string()));
    leaderboard.insert((2300, "Bob".to_string()));
    leaderboard.insert((1800, "Charlie".to_string()));
    leaderboard.insert((1200, "David".to_string()));
    leaderboard.insert((2500, "Eve".to_string()));
    
    println!("排行榜（按分数升序）:");
    for (i, (score, name)) in leaderboard.iter().into_iter().enumerate() {
        println!("第 {} 名: {} - {} 分", i + 1, name, score);
    }
    
    println!("\n高分玩家（2000 分以上）:");
    for (score, name) in leaderboard.range(&(2000, String::new()), &(9999, String::new())) {
        println!("  {} - {} 分", name, score);
    }
    
    println!("\n当前最高层数: {}", leaderboard.level());
    println!("总玩家数: {}", leaderboard.len());
}
