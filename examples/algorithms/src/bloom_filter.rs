//! # 布隆过滤器 (Bloom Filter)
//!
//! ## 算法描述
//! 布隆过滤器是一种空间效率极高的概率型数据结构，用于测试一个元素是否属于某个集合。
//!
//! ## 核心特性
//! - **可能存在误判**（False Positive）：可能将不在集合中的元素判断为存在
//! - **不会漏判**（False Negative）：不会将集合中的元素判断为不存在
//! - **空间效率**：相比哈希表，占用极少的内存
//!
//! ## 原理
//! - 使用一个位数组（bit array）和多个哈希函数
//! - 插入时：将元素经过 k 个哈希函数计算，将对应位置设为 1
//! - 查询时：检查所有 k 个位置是否都为 1
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | insert | O(k) | O(1) |
//! | contains | O(k) | O(1) |
//!
//! 其中 k 是哈希函数的数量
//!
//! ## 参数选择
//! - 预期元素数量：n
//! - 可接受的误判率：p
//! - 最优位数组大小：m = -n × ln(p) / (ln 2)²
//! - 最优哈希函数数量：k = m/n × ln 2

use std::hash::{Hash, Hasher};

/// 布隆过滤器结构
///
/// # 类型参数
/// - `T`: 元素类型，需要实现 Hash trait
///
/// # 示例
/// ```
/// use formal_algorithms::bloom_filter::BloomFilter;
///
/// // 创建预期存储 10000 个元素，误判率 1% 的布隆过滤器
/// let mut bf: BloomFilter<String> = BloomFilter::new(10000, 0.01);
///
/// bf.insert(&"hello".to_string());
/// bf.insert(&"world".to_string());
///
/// assert!(bf.contains(&"hello".to_string()));
/// assert!(bf.contains(&"world".to_string()));
/// assert!(!bf.contains(&"unknown".to_string())); // 大概率返回 false
/// ```
pub struct BloomFilter<T: Hash> {
    /// 位数组
    bits: Vec<bool>,
    /// 位数组大小
    size: usize,
    /// 哈希函数数量
    hash_count: usize,
    /// 预期元素数量
    expected_items: usize,
    /// 可接受的误判率
    false_positive_rate: f64,
    /// 已插入元素数量
    item_count: usize,
    /// 种子值，用于不同的哈希函数
    seeds: Vec<u64>,
    /// 幽灵类型
    _marker: std::marker::PhantomData<T>,
}

impl<T: Hash> BloomFilter<T> {
    /// 创建布隆过滤器
    ///
    /// # 参数
    /// - `expected_items`: 预期要插入的元素数量
    /// - `false_positive_rate`: 可接受的误判率（0.0 ~ 1.0）
    ///
    /// # 公式
    /// 根据给定的 n（预期元素数）和 p（误判率），计算最优参数：
    /// - 位数组大小 m = -n × ln(p) / (ln 2)²
    /// - 哈希函数数量 k = m/n × ln 2
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::bloom_filter::BloomFilter;
    ///
    /// // 存储 100 万个元素，误判率 0.1%
    /// let mut bf: BloomFilter<String> = BloomFilter::new(1_000_000, 0.001);
    /// ```
    pub fn new(expected_items: usize, false_positive_rate: f64) -> Self {
        assert!(
            false_positive_rate > 0.0 && false_positive_rate < 1.0,
            "误判率必须在 (0, 1) 之间"
        );
        assert!(expected_items > 0, "预期元素数量必须大于 0");

        // 计算最优位数组大小
        // m = -n * ln(p) / (ln 2)^2
        let ln2 = std::f64::consts::LN_2;
        let size = ((-1.0f64)
            * expected_items as f64
            * false_positive_rate.ln()
            / (ln2 * ln2))
            .ceil() as usize;
        let size = size.max(1);

        // 计算最优哈希函数数量
        // k = m/n * ln 2
        let hash_count = ((size as f64 / expected_items as f64) * ln2)
            .round()
            .max(1.0) as usize;

        // 生成不同的种子值
        let seeds: Vec<u64> = (0..hash_count)
            .map(|i| 0x9e3779b97f4a7c15u64.wrapping_add((i as u64).wrapping_mul(0xbf58476d1ce4e5b9)))
            .collect();

        Self {
            bits: vec![false; size],
            size,
            hash_count,
            expected_items,
            false_positive_rate,
            item_count: 0,
            seeds,
            _marker: std::marker::PhantomData,
        }
    }

    /// 插入元素
    ///
    /// # 参数
    /// - `item`: 要插入的元素
    ///
    /// # 复杂度
    /// - 时间复杂度：O(k)，k 是哈希函数数量
    pub fn insert(&mut self, item: &T) {
        for i in 0..self.hash_count {
            let index = self.hash(item, i) % self.size;
            self.bits[index] = true;
        }
        self.item_count += 1;
    }

    /// 检查元素是否可能存在
    ///
    /// # 参数
    /// - `item`: 要检查的元素
    ///
    /// # 返回值
    /// - `true`: 元素可能存在（可能有误判）
    /// - `false`: 元素肯定不存在（不会误判）
    ///
    /// # 复杂度
    /// - 时间复杂度：O(k)
    pub fn contains(&self, item: &T) -> bool {
        for i in 0..self.hash_count {
            let index = self.hash(item, i) % self.size;
            if !self.bits[index] {
                return false;
            }
        }
        true
    }

    /// 检查并插入（如果不存在）
    ///
    /// # 返回值
    /// - `true`: 元素可能已经存在
    /// - `false`: 元素肯定不存在，并已插入
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::bloom_filter::BloomFilter;
    ///
    /// let mut bf: BloomFilter<&str> = BloomFilter::new(100, 0.01);
    ///
    /// // 第一次，肯定不存在
    /// assert!(!bf.check_and_insert("hello"));
    ///
    /// // 第二次，已经存在
    /// assert!(bf.check_and_insert("hello"));
    /// ```
    pub fn check_and_insert(&mut self, item: T) -> bool 
    where
        T: Clone,
    {
        let exists = self.contains(&item);
        if !exists {
            self.insert(&item);
        }
        exists
    }

    /// 清空过滤器
    pub fn clear(&mut self) {
        self.bits.fill(false);
        self.item_count = 0;
    }

    /// 返回当前元素数量（可能有计数不准确的情况，如果有重复插入）
    pub fn len(&self) -> usize {
        self.item_count
    }

    /// 检查是否为空
    pub fn is_empty(&self) -> bool {
        self.item_count == 0
    }

    /// 返回位数组大小
    pub fn bit_size(&self) -> usize {
        self.size
    }

    /// 返回哈希函数数量
    pub fn hash_count(&self) -> usize {
        self.hash_count
    }

    /// 返回当前预估的误判率
    ///
    /// 公式：(1 - e^(-kn/m))^k
    /// 其中 n 是已插入元素数，m 是位数组大小，k 是哈希函数数量
    pub fn current_false_positive_rate(&self) -> f64 {
        let n = self.item_count as f64;
        let m = self.size as f64;
        let k = self.hash_count as f64;

        (1.0 - (-k * n / m).exp()).powf(k)
    }

    /// 返回预期的误判率
    pub fn expected_false_positive_rate(&self) -> f64 {
        self.false_positive_rate
    }

    /// 计算多个哈希值
    fn hash(&self, item: &T, seed_index: usize) -> usize {
        use std::collections::hash_map::DefaultHasher;
        
        let seed = self.seeds[seed_index];
        let mut hasher = DefaultHasher::new();
        
        // 将种子和元素一起哈希
        seed.hash(&mut hasher);
        item.hash(&mut hasher);
        
        let result = hasher.finish() as usize;
        // 防止溢出
        result % self.size
    }

    /// 将位数组打包为字节（用于序列化）
    pub fn to_bytes(&self) -> Vec<u8> {
        let byte_size = (self.size + 7) / 8;
        let mut bytes = vec![0u8; byte_size];
        
        for (i, &bit) in self.bits.iter().enumerate() {
            if bit {
                bytes[i / 8] |= 1 << (i % 8);
            }
        }
        
        bytes
    }

    /// 从字节重建布隆过滤器（反序列化）
    ///
    /// 注意：需要知道原始参数才能正确重建
    pub fn from_bytes(
        bytes: &[u8],
        expected_items: usize,
        false_positive_rate: f64,
    ) -> Self {
        let mut filter = Self::new(expected_items, false_positive_rate);
        let bit_size = filter.size;
        
        filter.bits.clear();
        for i in 0..bit_size {
            let byte_idx = i / 8;
            let bit_idx = i % 8;
            if byte_idx < bytes.len() {
                filter.bits.push((bytes[byte_idx] >> bit_idx) & 1 == 1);
            } else {
                filter.bits.push(false);
            }
        }
        
        filter
    }
}

impl<T: Hash> Clone for BloomFilter<T> {
    fn clone(&self) -> Self {
        Self {
            bits: self.bits.clone(),
            size: self.size,
            hash_count: self.hash_count,
            expected_items: self.expected_items,
            false_positive_rate: self.false_positive_rate,
            item_count: self.item_count,
            seeds: self.seeds.clone(),
            _marker: std::marker::PhantomData,
        }
    }
}

/// 可计数的布隆过滤器（支持删除操作）
///
/// 使用计数器数组代替位数组，可以统计每个位置被设置了几次
pub struct CountingBloomFilter<T: Hash> {
    /// 计数器数组
    counters: Vec<u8>,
    /// 数组大小
    size: usize,
    /// 哈希函数数量
    hash_count: usize,
    /// 种子值
    seeds: Vec<u64>,
    /// 元素计数
    item_count: usize,
    _marker: std::marker::PhantomData<T>,
}

impl<T: Hash> CountingBloomFilter<T> {
    /// 创建可计数的布隆过滤器
    ///
    /// 注意：计数器使用 u8，最大值为 255，超过会溢出
    pub fn new(expected_items: usize, false_positive_rate: f64) -> Self {
        let bf: BloomFilter<T> = BloomFilter::new(expected_items, false_positive_rate);
        
        Self {
            counters: vec![0; bf.bit_size()],
            size: bf.bit_size(),
            hash_count: bf.hash_count(),
            seeds: bf.seeds.clone(),
            item_count: 0,
            _marker: std::marker::PhantomData,
        }
    }

    /// 插入元素
    pub fn insert(&mut self, item: &T) {
        for i in 0..self.hash_count {
            let index = self.hash(item, i) % self.size;
            if self.counters[index] < u8::MAX {
                self.counters[index] += 1;
            }
        }
        self.item_count += 1;
    }

    /// 删除元素
    ///
    /// 注意：只能删除之前插入过的元素，否则可能产生误删
    pub fn remove(&mut self, item: &T) {
        for i in 0..self.hash_count {
            let index = self.hash(item, i) % self.size;
            if self.counters[index] > 0 {
                self.counters[index] -= 1;
            }
        }
        self.item_count = self.item_count.saturating_sub(1);
    }

    /// 检查元素是否存在
    pub fn contains(&self, item: &T) -> bool {
        for i in 0..self.hash_count {
            let index = self.hash(item, i) % self.size;
            if self.counters[index] == 0 {
                return false;
            }
        }
        true
    }

    /// 清空过滤器
    pub fn clear(&mut self) {
        self.counters.fill(0);
        self.item_count = 0;
    }

    fn hash(&self, item: &T, seed_index: usize) -> usize {
        use std::collections::hash_map::DefaultHasher;
        
        let seed = self.seeds[seed_index];
        let mut hasher = DefaultHasher::new();
        seed.hash(&mut hasher);
        item.hash(&mut hasher);
        hasher.finish() as usize
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic_operations() {
        let mut bf: BloomFilter<String> = BloomFilter::new(100, 0.01);
        
        bf.insert(&"hello".to_string());
        bf.insert(&"world".to_string());
        
        assert!(bf.contains(&"hello".to_string()));
        assert!(bf.contains(&"world".to_string()));
        assert!(!bf.contains(&"unknown".to_string()));
    }

    #[test]
    fn test_check_and_insert() {
        let mut bf: BloomFilter<i32> = BloomFilter::new(100, 0.01);
        
        // 第一次插入，返回 false（之前不存在）
        assert!(!bf.check_and_insert(42));
        
        // 第二次检查，返回 true（已经存在）
        assert!(bf.check_and_insert(42));
    }

    #[test]
    fn test_clear() {
        let mut bf: BloomFilter<String> = BloomFilter::new(100, 0.01);
        
        bf.insert(&&"test".to_string());
        assert!(bf.contains(&"test".to_string()));
        
        bf.clear();
        assert!(!bf.contains(&"test".to_string()));
        assert!(bf.is_empty());
    }

    #[test]
    fn test_false_positive_rate() {
        let expected_items = 1000;
        let target_rate = 0.01; // 1%
        
        let mut bf: BloomFilter<i32> = BloomFilter::new(expected_items, target_rate);
        
        // 插入元素
        for i in 0..expected_items {
            bf.insert(&(i as i32));
        }
        
        // 检查未插入的元素，统计误判率
        let mut false_positives = 0;
        let test_count = 10000;
        
        for i in expected_items..(expected_items + test_count) {
            if bf.contains(&(i as i32)) {
                false_positives += 1;
            }
        }
        
        let actual_rate = false_positives as f64 / test_count as f64;
        println!("预期误判率: {:.2}%", target_rate * 100.0);
        println!("实际误判率: {:.2}%", actual_rate * 100.0);
        
        // 实际误判率应该接近目标值（允许一定误差）
        assert!(actual_rate < target_rate * 3.0);
    }

    #[test]
    fn test_counting_bloom_filter() {
        let mut bf: CountingBloomFilter<String> = CountingBloomFilter::new(100, 0.01);
        
        bf.insert(&"test".to_string());
        assert!(bf.contains(&"test".to_string()));
        
        bf.remove(&"test".to_string());
        assert!(!bf.contains(&"test".to_string()));
    }

    #[test]
    fn test_large_dataset() {
        let items = 1_000_000;
        let mut bf: BloomFilter<i32> = BloomFilter::new(items, 0.001);
        
        // 插入 100 万个元素
        for i in 0..items {
            bf.insert(&(i as i32));
        }
        
        // 验证所有元素都存在
        for i in 0..items {
            assert!(bf.contains(&(i as i32)), "元素 {} 应该存在", i);
        }
        
        println!("位数组大小: {} bits ({:.2} MB)", 
            bf.bit_size(),
            bf.bit_size() as f64 / 8.0 / 1024.0 / 1024.0
        );
        println!("哈希函数数量: {}", bf.hash_count());
        println!("当前误判率: {:.4}%", bf.current_false_positive_rate() * 100.0);
    }

    #[test]
    fn test_serialization() {
        let mut bf: BloomFilter<String> = BloomFilter::new(100, 0.01);
        
        bf.insert(&"hello".to_string());
        bf.insert(&"world".to_string());
        
        let bytes = bf.to_bytes();
        let mut restored = BloomFilter::<String>::from_bytes(&bytes, 100, 0.01);
        
        assert!(restored.contains(&"hello".to_string()));
        assert!(restored.contains(&"world".to_string()));
        assert!(!restored.contains(&"unknown".to_string()));
    }

    #[test]
    fn test_parameter_calculation() {
        // 测试参数计算是否正确
        let bf: BloomFilter<i32> = BloomFilter::new(1000, 0.01);
        
        // 对于 n=1000, p=0.01:
        // m ≈ 9586 bits
        // k ≈ 7 hash functions
        assert!(bf.bit_size() > 9000 && bf.bit_size() < 10000);
        assert!(bf.hash_count() >= 6 && bf.hash_count() <= 8);
    }
}

/// 使用示例
///
/// ```
/// use formal_algorithms::bloom_filter::BloomFilter;
///
/// fn main() {
///     // 创建布隆过滤器，预期存储 100 万个 URL，误判率 0.1%
///     let mut bf: BloomFilter<String> = BloomFilter::new(1_000_000, 0.001);
///     
///     // 添加已访问的 URL
///     let urls = vec![
///         "https://example.com/page1",
///         "https://example.com/page2",
///         "https://example.com/page3",
///     ];
///     
///     for url in urls {
///         bf.insert(&url.to_string());
///     }
///     
///     // 检查 URL 是否已访问
///     println!("已访问 page1: {}", bf.contains(&"https://example.com/page1".to_string()));
///     println!("已访问 page4: {}", bf.contains(&"https://example.com/page4".to_string()));
///     
///     // 内存使用情况
///     println!("\n内存使用:");
///     println!("  位数组大小: {} bits", bf.bit_size());
///     println!("  约 {:.2} MB", bf.bit_size() as f64 / 8.0 / 1024.0 / 1024.0);
///     println!("  哈希函数数量: {}", bf.hash_count());
///     println!("  当前误判率: {:.4}%", bf.current_false_positive_rate() * 100.0);
/// }
/// ```
pub fn example_usage() {
    // 爬虫去重场景
    let mut crawled_urls: BloomFilter<String> = BloomFilter::new(10_000_000, 0.001);
    
    // 模拟爬取 URL
    let urls_to_crawl = vec![
        "https://example.com/1",
        "https://example.com/2",
        "https://example.com/3",
    ];
    
    for url in urls_to_crawl {
        if !crawled_urls.contains(&url.to_string()) {
            println!("爬取: {}", url);
            crawled_urls.insert(&url.to_string());
        } else {
            println!("跳过已爬取的 URL: {}", url);
        }
    }
    
    println!("\n布隆过滤器统计:");
    println!("已记录 URL 数: {}", crawled_urls.len());
    println!("位数组大小: {} bits", crawled_urls.bit_size());
    println!("预估误判率: {:.4}%", crawled_urls.current_false_positive_rate() * 100.0);
}
