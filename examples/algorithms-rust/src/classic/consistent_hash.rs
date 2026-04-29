//! # 一致性哈希 (Consistent Hashing)
//!
//! ## 算法描述
//! 一致性哈希是一种特殊的哈希算法，在分布式系统中用于解决数据分布和节点增减时的数据迁移问题。
//!
//! ## 核心思想
//! - 将数据和节点都映射到一个环形的哈希空间上
//! - 数据存储在顺时针方向的第一个节点上
//! - 使用虚拟节点解决数据分布不均匀问题
//!
//! ## 为什么需要一致性哈希？
//! 传统哈希：hash(key) % N，当 N 变化时，几乎所有数据都要重新映射
//! 一致性哈希：节点变化只影响相邻节点的数据，迁移量大幅减少
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 说明 |
//! |------|-----------|------|
//! | add_node | O(V log V) | V 是虚拟节点数量 |
//! | remove_node | O(V log V) | |
//! | get_node | O(log N) | N 是虚拟节点总数 |
//!
//! ## 空间复杂度
//! - O(N × V)：N 是物理节点数，V 是每个物理节点的虚拟节点数

use std::collections::{BTreeMap, HashMap};
use std::hash::{Hash, Hasher};

/// 默认虚拟节点数量
const DEFAULT_VIRTUAL_NODES: usize = 150;

/// 一致性哈希环
///
/// # 类型参数
/// - `T`: 节点类型，需要实现 Clone + Eq + Hash
///
/// # 示例
/// ```
/// use formal_algorithms::consistent_hash::ConsistentHash;
///
/// let mut ch = ConsistentHash::new();
/// ch.add_node("server1");
/// ch.add_node("server2");
/// 
/// let node = ch.get_node(&"user:123");
/// ```
pub struct ConsistentHash<T> {
    /// 哈希环：哈希值 -> 节点
    ring: BTreeMap<u64, T>,
    /// 物理节点到虚拟节点的映射
    physical_nodes: HashMap<T, Vec<u64>>,
    /// 每个物理节点的虚拟节点数量
    virtual_nodes: usize,
    /// 使用的哈希函数
    hasher: Box<dyn Fn(&[u8]) -> u64 + Send + Sync>,
}

impl<T> ConsistentHash<T>
where
    T: Clone + Eq + Hash + std::fmt::Debug,
{
    /// 创建默认配置的一致性哈希
    ///
    /// # 默认配置
    /// - 虚拟节点数：150
    /// - 哈希函数：默认的 std::collections::hash_map::DefaultHasher
    pub fn new() -> Self {
        Self::with_virtual_nodes(DEFAULT_VIRTUAL_NODES)
    }

    /// 创建指定虚拟节点数量的一致性哈希
    ///
    /// # 参数
    /// - `virtual_nodes`: 每个物理节点的虚拟节点数量
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::consistent_hash::ConsistentHash;
    ///
    /// let ch: ConsistentHash<String> = ConsistentHash::with_virtual_nodes(200);
    /// ```
    pub fn with_virtual_nodes(virtual_nodes: usize) -> Self {
        Self {
            ring: BTreeMap::new(),
            physical_nodes: HashMap::new(),
            virtual_nodes,
            hasher: Box::new(|bytes| {
                use std::collections::hash_map::DefaultHasher;
                let mut hasher = DefaultHasher::new();
                bytes.hash(&mut hasher);
                hasher.finish()
            }),
        }
    }

    /// 添加节点到哈希环
    ///
    /// # 参数
    /// - `node`: 要添加的节点
    ///
    /// # 说明
    /// 为每个物理节点创建多个虚拟节点，分散在哈希环上
    ///
    /// # 复杂度
    /// - 时间复杂度：O(V log V)，V 是虚拟节点数量
    pub fn add_node(&mut self, node: T) {
        if self.physical_nodes.contains_key(&node) {
            return; // 节点已存在
        }

        let mut virtual_hashes = Vec::with_capacity(self.virtual_nodes);

        for i in 0..self.virtual_nodes {
            // 为虚拟节点生成唯一标识
            let virtual_key = format!("{:?}:{}:{}", node, i, self.virtual_nodes);
            let hash = (self.hasher)(virtual_key.as_bytes());
            
            self.ring.insert(hash, node.clone());
            virtual_hashes.push(hash);
        }

        self.physical_nodes.insert(node, virtual_hashes);
    }

    /// 从哈希环中移除节点
    ///
    /// # 参数
    /// - `node`: 要移除的节点
    ///
    /// # 复杂度
    /// - 时间复杂度：O(V log V)
    pub fn remove_node(&mut self, node: &T) {
        if let Some(virtual_hashes) = self.physical_nodes.remove(node) {
            for hash in virtual_hashes {
                self.ring.remove(&hash);
            }
        }
    }

    /// 获取键对应的节点
    ///
    /// # 参数
    /// - `key`: 要查找的键
    ///
    /// # 返回值
    /// - `Some(&T)`: 对应的节点
    /// - `None`: 如果哈希环为空
    ///
    /// # 说明
    /// 使用顺时针查找，找到第一个大于等于 key 哈希值的节点
    /// 如果没有找到，则返回环上的第一个节点
    ///
    /// # 复杂度
    /// - 时间复杂度：O(log N)，N 是虚拟节点总数
    pub fn get_node<K: Hash>(&self, key: &K) -> Option<&T> {
        if self.ring.is_empty() {
            return None;
        }

        let hash = self.hash_key(key);
        
        // 使用 BTreeMap 的范围查询找到第一个大于等于 hash 的节点
        self.ring
            .range(hash..)
            .next()
            .or_else(|| self.ring.iter().next())
            .map(|(_, node)| node)
    }

    /// 获取多个候选节点（用于副本存储）
    ///
    /// # 参数
    /// - `key`: 要查找的键
    /// - `replicas`: 副本数量
    ///
    /// # 返回值
    /// - 唯一节点的列表，数量可能少于 replicas（如果节点不足）
    ///
    /// # 复杂度
    /// - 时间复杂度：O(replicas × log N)
    pub fn get_nodes<K: Hash>(&self, key: &K, replicas: usize) -> Vec<&T> {
        if self.ring.is_empty() || replicas == 0 {
            return Vec::new();
        }

        let hash = self.hash_key(key);
        let mut result = Vec::with_capacity(replicas);
        let mut seen = std::collections::HashSet::new();

        // 从 hash 位置开始顺时针查找
        for (_, node) in self.ring.range(hash..).chain(self.ring.iter()) {
            if seen.insert(format!("{:?}", node)) {
                result.push(node);
                if result.len() >= replicas {
                    break;
                }
            }
        }

        result
    }

    /// 检查节点是否存在
    pub fn contains_node(&self, node: &T) -> bool {
        self.physical_nodes.contains_key(node)
    }

    /// 返回物理节点数量
    pub fn node_count(&self) -> usize {
        self.physical_nodes.len()
    }

    /// 返回虚拟节点总数
    pub fn virtual_node_count(&self) -> usize {
        self.ring.len()
    }

    /// 返回所有物理节点
    pub fn nodes(&self) -> impl Iterator<Item = &T> {
        self.physical_nodes.keys()
    }

    /// 检查哈希环是否为空
    pub fn is_empty(&self) -> bool {
        self.physical_nodes.is_empty()
    }

    /// 计算键的哈希值
    fn hash_key<K: Hash>(&self, key: &K) -> u64 {
        use std::collections::hash_map::DefaultHasher;
        let mut hasher = DefaultHasher::new();
        key.hash(&mut hasher);
        hasher.finish()
    }

    /// 自定义哈希函数
    ///
    /// # 参数
    /// - `hasher`: 哈希函数，接受字节切片返回 u64
    pub fn with_hasher<F>(mut self, hasher: F) -> Self
    where
        F: Fn(&[u8]) -> u64 + Send + Sync + 'static,
    {
        self.hasher = Box::new(hasher);
        self
    }
}

impl<T> Default for ConsistentHash<T>
where
    T: Clone + Eq + Hash + std::fmt::Debug,
{
    fn default() -> Self {
        Self::new()
    }
}

/// 节点统计信息
#[derive(Debug, Clone)]
pub struct NodeStats {
    pub node: String,
    pub virtual_nodes: usize,
    pub percentage: f64,
}

/// 统计哈希环上各节点的数据分布
pub fn analyze_distribution<T: Clone + Eq + Hash + std::fmt::Debug>(
    ch: &ConsistentHash<T>,
    sample_keys: &[String],
) -> HashMap<String, usize> {
    let mut distribution: HashMap<String, usize> = HashMap::new();

    for key in sample_keys {
        if let Some(node) = ch.get_node(&key) {
            let key = format!("{:?}", node);
            *distribution.entry(key).or_insert(0) += 1;
        }
    }

    distribution
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        
        assert_eq!(ch.node_count(), 2);
        assert!(ch.contains_node(&"server1".to_string()));
        assert!(ch.contains_node(&"server2".to_string()));
    }

    #[test]
    fn test_get_node() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        
        // 所有键都应该映射到某个节点
        let node = ch.get_node(&"user:123");
        assert!(node.is_some());
        
        let node = ch.get_node(&"user:456");
        assert!(node.is_some());
    }

    #[test]
    fn test_remove_node() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        
        ch.remove_node(&"server1".to_string());
        
        assert_eq!(ch.node_count(), 1);
        assert!(!ch.contains_node(&"server1".to_string()));
        assert!(ch.contains_node(&"server2".to_string()));
    }

    #[test]
    fn test_empty_ring() {
        let ch: ConsistentHash<String> = ConsistentHash::new();
        
        assert!(ch.is_empty());
        assert_eq!(ch.get_node(&"key"), None);
    }

    #[test]
    fn test_duplicate_node() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server1".to_string()); // 重复添加
        
        assert_eq!(ch.node_count(), 1);
    }

    #[test]
    fn test_get_nodes_for_replicas() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        ch.add_node("server3".to_string());
        
        let nodes = ch.get_nodes(&"key", 2);
        assert_eq!(nodes.len(), 2);
        
        let nodes = ch.get_nodes(&"key", 5); // 超过节点数
        assert_eq!(nodes.len(), 3); // 只能返回 3 个
    }

    #[test]
    fn test_consistency() {
        let mut ch = ConsistentHash::new();
        
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        
        // 多次获取同一键应该返回相同节点
        let node1 = ch.get_node(&"user:123").cloned();
        let node2 = ch.get_node(&"user:123").cloned();
        
        assert_eq!(node1, node2);
    }

    #[test]
    fn test_virtual_nodes_distribution() {
        let ch = ConsistentHash::with_virtual_nodes(100);
        
        // 虚拟节点数应该是 0，因为没有物理节点
        assert_eq!(ch.virtual_node_count(), 0);
        
        let mut ch = ch;
        ch.add_node("server1".to_string());
        
        // 现在应该有 100 个虚拟节点
        assert_eq!(ch.virtual_node_count(), 100);
    }

    #[test]
    fn test_node_addition_minimal_migration() {
        let mut ch = ConsistentHash::with_virtual_nodes(50);
        
        // 初始有 2 个节点
        ch.add_node("server1".to_string());
        ch.add_node("server2".to_string());
        
        // 记录每个键对应的节点
        let keys: Vec<String> = (0..1000).map(|i| format!("key:{}", i)).collect();
        let initial_mapping: HashMap<String, String> = keys
            .iter()
            .map(|k| (k.clone(), format!("{:?}", ch.get_node(k).unwrap())))
            .collect();
        
        // 添加新节点
        ch.add_node("server3".to_string());
        
        // 计算变化的键数量
        let mut changed = 0;
        for key in &keys {
            let new_node = format!("{:?}", ch.get_node(key).unwrap());
            if initial_mapping[key] != new_node {
                changed += 1;
            }
        }
        
        // 理想情况下，只有约 1/3 的键需要迁移
        let change_ratio = changed as f64 / keys.len() as f64;
        assert!(change_ratio < 0.4, "变更比例应该小于 40%，实际是 {:.2}%", change_ratio * 100.0);
    }

    #[test]
    fn test_custom_hasher() {
        let ch = ConsistentHash::with_virtual_nodes(10)
            .with_hasher(|bytes| {
                // 简单的自定义哈希函数
                bytes.iter().map(|&b| b as u64).sum()
            });
        
        let mut ch = ch;
        ch.add_node("server1".to_string());
        
        assert!(ch.get_node(&"test").is_some());
    }
}

/// 使用示例
///
/// ```
/// use formal_algorithms::consistent_hash::{ConsistentHash, analyze_distribution};
///
/// fn main() {
///     // 创建一致性哈希环，每个物理节点 150 个虚拟节点
///     let mut ch = ConsistentHash::new();
///     
///     // 添加服务器节点
///     ch.add_node("192.168.1.1:8080".to_string());
///     ch.add_node("192.168.1.2:8080".to_string());
///     ch.add_node("192.168.1.3:8080".to_string());
///     
///     // 模拟用户请求
///     let user_ids = vec!["user:1", "user:2", "user:3", "user:4", "user:5"];
///     
///     for user_id in &user_ids {
///         let server = ch.get_node(&user_id.to_string());
///         println!("{} -> {:?}", user_id, server);
///     }
///     
///     // 添加新服务器（只影响少量用户）
///     println!("\n添加新服务器...");
///     ch.add_node("192.168.1.4:8080".to_string());
///     
///     // 分析数据分布
///     let test_keys: Vec<String> = (0..10000)
///         .map(|i| format!("key:{}", i))
///         .collect();
///     
///     let distribution = analyze_distribution(&ch, &test_keys);
///     println!("\n数据分布:");
///     for (server, count) in &distribution {
///         println!("{}: {} keys ({:.2}%)", server, count, 
///             *count as f64 / test_keys.len() as f64 * 100.0);
///     }
/// }
/// ```
pub fn example_usage() {
    let mut ch = ConsistentHash::new();
    
    // 添加缓存服务器
    ch.add_node("cache-server-1".to_string());
    ch.add_node("cache-server-2".to_string());
    ch.add_node("cache-server-3".to_string());
    
    // 为数据选择服务器
    let data_keys = vec!["session:1001", "session:1002", "session:1003"];
    
    for key in &data_keys {
        let server = ch.get_node(&key.to_string());
        println!("数据 {} 存储在 {:?}", key, server);
    }
    
    // 水平扩展时只需迁移少量数据
    println!("\n添加 cache-server-4...");
    ch.add_node("cache-server-4".to_string());
    
    println!("当前共有 {} 个物理节点", ch.node_count());
    println!("共有 {} 个虚拟节点", ch.virtual_node_count());
}
