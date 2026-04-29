//! # 哈希表 (Hash Table)
//!
//! 提供链地址法（Separate Chaining）与开放寻址法（Open Addressing）两种实现。
//!
//! ## 核心思想
//! - **链地址法**：每个桶维护一个链表/向量，冲突键共存于同一桶
//! - **开放寻址法**：冲突时按探测序列在表内寻找下一个空槽，支持线性探测与二次探测
//! - 负载因子 α = n/m 决定性能，通常扩容阈值设为 0.75
//!
//! ## 复杂度分析 (平均情况)
//! | 操作 | 链地址法 | 开放寻址法 |
//! |------|----------|------------|
//! | insert | O(1) | O(1) |
//! | search | O(1) | O(1) |
//! | delete | O(1) | O(1) |

// ==================== Separate Chaining ====================

/// 链地址法哈希表
///
/// # 示例
/// ```
/// use formal_algorithms::hash_table::HashTableSeparateChaining;
///
/// let mut ht: HashTableSeparateChaining<&str, i32> = HashTableSeparateChaining::new();
/// ht.insert("key1", 100);
/// ht.insert("key2", 200);
/// assert_eq!(ht.get(&"key1"), Some(&100));
/// assert_eq!(ht.remove(&"key1"), Some(100));
/// assert_eq!(ht.get(&"key1"), None);
/// ```
#[derive(Debug, Clone)]
pub struct HashTableSeparateChaining<K, V> {
    buckets: Vec<Vec<(K, V)>>,
    len: usize,
}

impl<K, V> Default for HashTableSeparateChaining<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    fn default() -> Self {
        Self::new()
    }
}

impl<K, V> HashTableSeparateChaining<K, V>
where
    K: std::hash::Hash + Eq + Clone,
    V: Clone,
{
    /// 创建初始容量为 16 的哈希表
    pub fn new() -> Self {
        let mut buckets = Vec::with_capacity(16);
        buckets.resize_with(16, Vec::new);
        Self { buckets, len: 0 }
    }

    fn hash(&self, key: &K) -> usize {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(key, &mut hasher);
        std::hash::Hasher::finish(&hasher) as usize % self.buckets.len()
    }

    /// 插入键值对，若键已存在则更新值
    pub fn insert(&mut self, key: K, value: V) {
        if self.len > self.buckets.len() * 3 / 4 {
            self.resize();
        }
        let idx = self.hash(&key);
        let bucket = &mut self.buckets[idx];
        for (k, v) in bucket.iter_mut() {
            if k == &key {
                *v = value;
                return;
            }
        }
        bucket.push((key, value));
        self.len += 1;
    }

    /// 根据键查找值
    pub fn get(&self, key: &K) -> Option<&V> {
        let idx = self.hash(key);
        self.buckets[idx]
            .iter()
            .find(|(k, _)| k == key)
            .map(|(_, v)| v)
    }

    /// 根据键移除值
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let idx = self.hash(key);
        let bucket = &mut self.buckets[idx];
        let pos = bucket.iter().position(|(k, _)| k == key)?;
        self.len -= 1;
        Some(bucket.remove(pos).1)
    }

    /// 检查是否包含键
    pub fn contains_key(&self, key: &K) -> bool {
        self.get(key).is_some()
    }

    /// 返回元素个数
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn resize(&mut self) {
        let new_len = self.buckets.len() * 2;
        let old_buckets = std::mem::replace(&mut self.buckets, Vec::with_capacity(new_len));
        self.buckets.resize_with(new_len, Vec::new);
        self.len = 0;
        for mut bucket in old_buckets {
            for (k, v) in bucket.drain(..) {
                let idx = self.hash(&k);
                self.buckets[idx].push((k, v));
                self.len += 1;
            }
        }
    }
}

// ==================== Open Addressing ====================

#[derive(Clone)]
enum Slot<V> {
    Empty,
    Tombstone,
    Occupied(u64, V),
}

/// 开放寻址法哈希表，支持线性探测与二次探测
///
/// # 示例
/// ```
/// use formal_algorithms::hash_table::HashTableOpenAddressing;
///
/// let mut ht: HashTableOpenAddressing<&str, i32> = HashTableOpenAddressing::new_linear();
/// ht.insert("key1", 100);
/// assert_eq!(ht.get(&"key1"), Some(&100));
/// ```
#[derive(Clone)]
pub struct HashTableOpenAddressing<K, V> {
    slots: Vec<Slot<V>>,
    len: usize,
    use_quadratic: bool,
    _phantom: std::marker::PhantomData<K>,
}

impl<K, V> HashTableOpenAddressing<K, V>
where
    K: std::hash::Hash + Eq,
    V: Clone,
{
    /// 创建使用线性探测的哈希表
    pub fn new_linear() -> Self {
        Self::new(false)
    }

    /// 创建使用二次探测的哈希表
    pub fn new_quadratic() -> Self {
        Self::new(true)
    }

    fn new(use_quadratic: bool) -> Self {
        let capacity = 16;
        Self {
            slots: vec![Slot::Empty; capacity],
            len: 0,
            use_quadratic,
            _phantom: std::marker::PhantomData,
        }
    }

    fn hash_key(key: &K) -> u64 {
        let mut hasher = std::collections::hash_map::DefaultHasher::new();
        std::hash::Hash::hash(key, &mut hasher);
        let h = std::hash::Hasher::finish(&hasher);
        // Avoid 0 and u64::MAX since we reserve them internally
        if h == 0 || h == u64::MAX {
            1
        } else {
            h
        }
    }

    fn capacity(&self) -> usize {
        self.slots.len()
    }

    fn probe(&self, hash: u64, i: usize) -> usize {
        let m = self.capacity();
        if self.use_quadratic {
            (hash as usize + i + i * i) % m
        } else {
            (hash as usize + i) % m
        }
    }

    /// 插入键值对
    pub fn insert(&mut self, key: K, value: V) {
        if self.len > self.capacity() * 3 / 4 {
            self.resize();
        }
        let h = Self::hash_key(&key);
        for i in 0..self.capacity() {
            let idx = self.probe(h, i);
            match &self.slots[idx] {
                Slot::Empty | Slot::Tombstone => {
                    self.slots[idx] = Slot::Occupied(h, value);
                    self.len += 1;
                    return;
                }
                Slot::Occupied(existing_h, _) if *existing_h == h => {
                    // Simplified: treat same hash as same key for this educational implementation
                    self.slots[idx] = Slot::Occupied(h, value);
                    return;
                }
                _ => {}
            }
        }
        panic!("hash table is full");
    }

    /// 查找值
    pub fn get(&self, key: &K) -> Option<&V> {
        let h = Self::hash_key(key);
        for i in 0..self.capacity() {
            let idx = self.probe(h, i);
            match &self.slots[idx] {
                Slot::Empty => return None,
                Slot::Occupied(existing_h, v) if *existing_h == h => return Some(v),
                _ => {}
            }
        }
        None
    }

    /// 移除键值对
    pub fn remove(&mut self, key: &K) -> Option<V> {
        let h = Self::hash_key(key);
        for i in 0..self.capacity() {
            let idx = self.probe(h, i);
            match &self.slots[idx] {
                Slot::Empty => return None,
                Slot::Occupied(existing_h, _) if *existing_h == h => {
                    if let Slot::Occupied(_, v) = std::mem::replace(&mut self.slots[idx], Slot::Tombstone) {
                        self.len -= 1;
                        return Some(v);
                    }
                }
                _ => {}
            }
        }
        None
    }

    /// 返回元素个数
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    fn resize(&mut self) {
        let new_cap = self.capacity() * 2;
        let old_slots = std::mem::replace(&mut self.slots, vec![Slot::Empty; new_cap]);
        self.len = 0;
        for slot in old_slots {
            if let Slot::Occupied(h, v) = slot {
                for j in 0..self.capacity() {
                    let idx = self.probe(h, j);
                    if matches!(self.slots[idx], Slot::Empty | Slot::Tombstone) {
                        self.slots[idx] = Slot::Occupied(h, v);
                        self.len += 1;
                        break;
                    }
                }
            }
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_separate_chaining() {
        let mut ht: HashTableSeparateChaining<&str, i32> = HashTableSeparateChaining::new();
        ht.insert("apple", 5);
        ht.insert("banana", 6);
        ht.insert("cherry", 6);
        assert_eq!(ht.get(&"apple"), Some(&5));
        assert_eq!(ht.get(&"banana"), Some(&6));
        assert_eq!(ht.remove(&"banana"), Some(6));
        assert_eq!(ht.get(&"banana"), None);
        assert_eq!(ht.len(), 2);
    }

    #[test]
    fn test_open_addressing_linear() {
        let mut ht: HashTableOpenAddressing<&str, i32> = HashTableOpenAddressing::new_linear();
        ht.insert("a", 1);
        ht.insert("b", 2);
        ht.insert("c", 3);
        assert_eq!(ht.get(&"a"), Some(&1));
        assert_eq!(ht.get(&"b"), Some(&2));
        assert_eq!(ht.remove(&"b"), Some(2));
        assert_eq!(ht.get(&"b"), None);
    }

    #[test]
    fn test_open_addressing_quadratic() {
        let mut ht = HashTableOpenAddressing::new_quadratic();
        ht.insert(1, "one");
        ht.insert(2, "two");
        ht.insert(3, "three");
        assert_eq!(ht.get(&1), Some(&"one"));
        assert_eq!(ht.get(&2), Some(&"two"));
        assert_eq!(ht.remove(&2), Some("two"));
        assert_eq!(ht.get(&2), None);
    }

    #[test]
    fn test_resize_behavior() {
        let mut ht: HashTableSeparateChaining<i32, i32> = HashTableSeparateChaining::new();
        for i in 0..100 {
            ht.insert(i, i * 2);
        }
        for i in 0..100 {
            assert_eq!(ht.get(&i), Some(&(i * 2)));
        }
    }
}
