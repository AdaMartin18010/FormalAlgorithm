//! # LRU 缓存 (Least Recently Used Cache)
//!
//! ## 算法描述
//! LRU 缓存是一种常用的缓存淘汰策略，当缓存满时，优先淘汰最久未使用的数据。
//!
//! ## 核心思想
//! - 使用 **HashMap** 提供 O(1) 的查找能力
//! - 使用 **双向链表** 维护数据的访问顺序，链表头部是最新访问的，尾部是最久未访问的
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | get  | O(1)      | O(1)      |
//! | put  | O(1)      | O(1)      |
//!
//! ## 空间复杂度
//! - O(capacity)：存储最多 capacity 个键值对

use std::collections::HashMap;
use std::ptr::NonNull;

/// 双向链表节点
struct Node<K, V> {
    key: K,
    value: V,
    prev: Option<NonNull<Node<K, V>>>,
    next: Option<NonNull<Node<K, V>>>,
}

impl<K, V> Node<K, V> {
    /// 创建新节点
    fn new(key: K, value: V) -> Self {
        Self {
            key,
            value,
            prev: None,
            next: None,
        }
    }
}

/// LRU 缓存结构
///
/// # 示例
/// ```
/// use formal_algorithms::lru_cache::LruCache;
///
/// let mut cache = LruCache::new(2);
/// cache.put(1, "a");
/// cache.put(2, "b");
/// assert_eq!(cache.get(&1), Some(&"a"));
/// cache.put(3, "c"); // 淘汰键 2
/// assert_eq!(cache.get(&2), None);
/// ```
pub struct LruCache<K, V> {
    /// 存储键到节点指针的映射
    map: HashMap<K, NonNull<Node<K, V>>>,
    /// 双向链表虚拟头节点（最新访问）
    head: Option<NonNull<Node<K, V>>>,
    /// 双向链表虚拟尾节点（最久未访问）
    tail: Option<NonNull<Node<K, V>>>,
    /// 缓存容量
    capacity: usize,
    /// 当前大小
    size: usize,
}

impl<K, V> LruCache<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    /// 创建指定容量的 LRU 缓存
    ///
    /// # 参数
    /// - `capacity`: 缓存最大容量
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::lru_cache::LruCache;
    ///
    /// let cache: LruCache<i32, String> = LruCache::new(100);
    /// ```
    pub fn new(capacity: usize) -> Self {
        // 使用 MaybeUninit 来创建虚拟头尾节点，避免需要 Default
        
        
        let mut cache = Self {
            map: HashMap::with_capacity(capacity),
            head: None,
            tail: None,
            capacity,
            size: 0,
        };
        
        // 创建虚拟头尾节点 - 使用 MaybeUninit 避免初始化
        let head: *mut Node<K, V> = unsafe { 
            std::alloc::alloc(std::alloc::Layout::new::<Node<K, V>>()) as *mut Node<K, V>
        };
        let tail: *mut Node<K, V> = unsafe { 
            std::alloc::alloc(std::alloc::Layout::new::<Node<K, V>>()) as *mut Node<K, V>
        };
        
        unsafe {
            // 初始化节点的指针字段
            std::ptr::addr_of_mut!((*head).prev).write(None);
            std::ptr::addr_of_mut!((*head).next).write(None);
            std::ptr::addr_of_mut!((*tail).prev).write(None);
            std::ptr::addr_of_mut!((*tail).next).write(None);
            
            (*head).next = Some(NonNull::new_unchecked(tail));
            (*tail).prev = Some(NonNull::new_unchecked(head));
        }
        
        cache.head = Some(NonNull::new(head).unwrap());
        cache.tail = Some(NonNull::new(tail).unwrap());
        
        cache
    }

    /// 获取缓存中的值，并将其移动到链表头部（表示最近使用）
    ///
    /// # 参数
    /// - `key`: 要查找的键
    ///
    /// # 返回值
    /// - `Some(&V)`：如果键存在，返回值的引用
    /// - `None`：如果键不存在
    ///
    /// # 复杂度
    /// - 时间复杂度：O(1)
    pub fn get(&mut self, key: &K) -> Option<&V> {
        if let Some(&node_ptr) = self.map.get(key) {
            // 移动到头部
            unsafe {
                self.move_to_head(node_ptr);
                Some(&(*node_ptr.as_ptr()).value)
            }
        } else {
            None
        }
    }

    /// 获取可变引用
    ///
    /// # 复杂度
    /// - 时间复杂度：O(1)
    pub fn get_mut(&mut self, key: &K) -> Option<&mut V> {
        if let Some(&node_ptr) = self.map.get(key) {
            unsafe {
                self.move_to_head(node_ptr);
                Some(&mut (*node_ptr.as_ptr()).value)
            }
        } else {
            None
        }
    }

    /// 插入键值对
    ///
    /// # 参数
    /// - `key`: 键
    /// - `value`: 值
    ///
    /// # 说明
    /// - 如果键已存在，更新值并移动到头部
    /// - 如果键不存在，插入新节点
    /// - 如果缓存已满，淘汰尾部节点（最久未使用）
    ///
    /// # 复杂度
    /// - 时间复杂度：O(1)
    pub fn put(&mut self, key: K, value: V) {
        // 如果容量为 0，不插入任何元素
        if self.capacity == 0 {
            return;
        }

        // 如果键已存在，更新值并移动到头部
        if let Some(&node_ptr) = self.map.get(&key) {
            unsafe {
                (*node_ptr.as_ptr()).value = value;
                self.move_to_head(node_ptr);
            }
            return;
        }

        // 如果缓存已满，淘汰尾部节点
        if self.size >= self.capacity {
            self.remove_tail();
        }

        // 创建新节点并添加到头部
        let new_node = Box::new(Node::new(key.clone(), value));
        let node_ptr = NonNull::new(Box::into_raw(new_node)).unwrap();
        
        unsafe {
            self.add_to_head(node_ptr);
        }
        
        self.map.insert(key, node_ptr);
        self.size += 1;
    }

    /// 检查缓存是否包含指定键（不更新访问顺序）
    ///
    /// # 复杂度
    /// - 时间复杂度：O(1)
    pub fn contains_key(&self, key: &K) -> bool {
        self.map.contains_key(key)
    }

    /// 返回当前缓存大小
    pub fn len(&self) -> usize {
        self.size
    }

    /// 检查缓存是否为空
    pub fn is_empty(&self) -> bool {
        self.size == 0
    }

    /// 清空缓存
    pub fn clear(&mut self) {
        // 安全地释放所有节点内存
        for &node_ptr in self.map.values() {
            unsafe {
                let _ = Box::from_raw(node_ptr.as_ptr());
            }
        }
        self.map.clear();
        self.size = 0;
        
        // 重置链表
        unsafe {
            if let Some(head) = self.head {
                (*head.as_ptr()).next = self.tail;
            }
            if let Some(tail) = self.tail {
                (*tail.as_ptr()).prev = self.head;
            }
        }
    }

    /// 将节点移动到链表头部
    unsafe fn move_to_head(&mut self, node: NonNull<Node<K, V>>) {
        self.remove_node(node);
        self.add_to_head(node);
    }

    /// 从链表中移除节点
    unsafe fn remove_node(&mut self, node: NonNull<Node<K, V>>) {
        let node_ref = &mut *node.as_ptr();
        
        if let Some(prev) = node_ref.prev {
            (*prev.as_ptr()).next = node_ref.next;
        }
        if let Some(next) = node_ref.next {
            (*next.as_ptr()).prev = node_ref.prev;
        }
    }

    /// 添加节点到链表头部
    unsafe fn add_to_head(&mut self, node: NonNull<Node<K, V>>) {
        let head = self.head.unwrap();
        let first = (*head.as_ptr()).next.unwrap();
        
        (*node.as_ptr()).prev = Some(head);
        (*node.as_ptr()).next = Some(first);
        (*head.as_ptr()).next = Some(node);
        (*first.as_ptr()).prev = Some(node);
    }

    /// 移除链表尾部节点（最久未使用）
    fn remove_tail(&mut self) {
        unsafe {
            let tail = self.tail.unwrap();
            let last = (*tail.as_ptr()).prev.unwrap();
            
            // 跳过虚拟头节点
            if last == self.head.unwrap() {
                return;
            }
            
            let key = (*last.as_ptr()).key.clone();
            self.remove_node(last);
            self.map.remove(&key);
            let _ = Box::from_raw(last.as_ptr());
            self.size -= 1;
        }
    }
}

impl<K, V> Drop for LruCache<K, V> {
    fn drop(&mut self) {
        use std::alloc::{self, Layout};
        
        // 安全地释放所有节点内存
        for &node_ptr in self.map.values() {
            unsafe {
                let layout = Layout::new::<Node<K, V>>();
                alloc::dealloc(node_ptr.as_ptr() as *mut u8, layout);
            }
        }
        self.map.clear();
        self.size = 0;
        
        // 释放虚拟头尾节点
        unsafe {
            let layout = Layout::new::<Node<K, V>>();
            if let Some(head) = self.head {
                alloc::dealloc(head.as_ptr() as *mut u8, layout);
            }
            if let Some(tail) = self.tail {
                alloc::dealloc(tail.as_ptr() as *mut u8, layout);
            }
        }
    }
}

// 手动实现 Send 和 Sync（因为使用了原始指针）
unsafe impl<K: Send, V: Send> Send for LruCache<K, V> {}
unsafe impl<K: Sync, V: Sync> Sync for LruCache<K, V> {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut cache = LruCache::new(2);
        
        // 测试 put 和 get
        cache.put(1, "a");
        cache.put(2, "b");
        
        assert_eq!(cache.get(&1), Some(&"a"));
        assert_eq!(cache.get(&2), Some(&"b"));
        assert_eq!(cache.len(), 2);
    }

    #[test]
    fn test_lru_eviction() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, "a");
        cache.put(2, "b");
        cache.put(3, "c"); // 应该淘汰键 1
        
        assert_eq!(cache.get(&1), None); // 已被淘汰
        assert_eq!(cache.get(&2), Some(&"b"));
        assert_eq!(cache.get(&3), Some(&"c"));
    }

    #[test]
    fn test_access_updates_order() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, "a");
        cache.put(2, "b");
        
        // 访问键 1，使其变为最近使用
        cache.get(&1);
        
        // 添加新键，应该淘汰键 2（因为现在 1 是最近使用的）
        cache.put(3, "c");
        
        assert_eq!(cache.get(&1), Some(&"a")); // 仍然存在
        assert_eq!(cache.get(&2), None); // 已被淘汰
        assert_eq!(cache.get(&3), Some(&"c"));
    }

    #[test]
    fn test_update_existing_key() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, "a");
        cache.put(1, "updated"); // 更新值
        
        assert_eq!(cache.get(&1), Some(&"updated"));
        assert_eq!(cache.len(), 1); // 大小不变
    }

    #[test]
    fn test_get_mut() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, 10);
        
        if let Some(value) = cache.get_mut(&1) {
            *value = 20;
        }
        
        assert_eq!(cache.get(&1), Some(&20));
    }

    #[test]
    fn test_contains_key() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, "a");
        
        assert!(cache.contains_key(&1));
        assert!(!cache.contains_key(&2));
    }

    #[test]
    fn test_clear() {
        let mut cache = LruCache::new(2);
        
        cache.put(1, "a");
        cache.put(2, "b");
        cache.clear();
        
        assert!(cache.is_empty());
        assert_eq!(cache.get(&1), None);
        assert_eq!(cache.get(&2), None);
    }

    #[test]
    fn test_zero_capacity() {
        let mut cache = LruCache::new(0);
        
        cache.put(1, "a"); // 应该立即被淘汰
        
        assert!(cache.is_empty());
        assert_eq!(cache.get(&1), None);
    }

    #[test]
    fn test_large_capacity() {
        let mut cache = LruCache::new(1000);
        
        for i in 0..1000 {
            cache.put(i, i * 2);
        }
        
        assert_eq!(cache.len(), 1000);
        
        for i in 0..1000 {
            assert_eq!(cache.get(&i), Some(&(i * 2)));
        }
    }
}

/// 使用示例
/// 
/// ```
/// use formal_algorithms::lru_cache::LruCache;
///
/// fn main() {
///     // 创建容量为 3 的 LRU 缓存
///     let mut cache = LruCache::new(3);
///     
///     // 插入一些数据
///     cache.put("user:1", "Alice");
///     cache.put("user:2", "Bob");
///     cache.put("user:3", "Charlie");
///     
///     // 访问数据
///     println!("User 1: {:?}", cache.get(&"user:1")); // Some("Alice")
///     
///     // 添加新数据，触发淘汰
///     cache.put("user:4", "David"); // 淘汰 "user:2"
///     
///     println!("User 2: {:?}", cache.get(&"user:2")); // None（已被淘汰）
///     println!("User 4: {:?}", cache.get(&"user:4")); // Some("David")
/// }
/// ```
pub fn example_usage() {
    let mut cache = LruCache::new(3);
    
    cache.put("page:/home", "<html>Home</html>");
    cache.put("page:/about", "<html>About</html>");
    cache.put("page:/contact", "<html>Contact</html>");
    
    // 模拟访问
    println!("访问 /home: {:?}", cache.get(&"page:/home"));
    
    // 添加新页面
    cache.put("page:/products", "<html>Products</html>");
    
    // /about 应该被淘汰（因为 /home 被访问过，/contact 和 /products 是新的）
    println!("/about 是否被淘汰: {}", cache.get(&"page:/about").is_none());
}
