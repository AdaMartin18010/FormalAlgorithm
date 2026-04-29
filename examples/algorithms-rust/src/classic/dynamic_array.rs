//! # 动态数组 (Dynamic Array)
//!
//! 支持均摊 O(1) 尾部插入的自动扩容/缩容数组实现。
//!
//! ## 核心思想
//! - 当元素数量达到容量上限时，按 growth factor（通常为 2）扩容
//! - 当元素数量低于一定比例时，按相同因子缩容，避免空间浪费
//! - 使用 **势函数法** 可证明 n 次插入/删除的均摊代价为 O(1)
//!
//! ## 复杂度分析
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | push | O(1) 均摊 | O(n) |
//! | pop | O(1) 均摊 | O(n) |
//! | get/set | O(1) 最坏 | O(1) |
//! | insert/remove(at) | O(n) 最坏 | O(1) |

/// 动态数组
///
/// # 示例
/// ```
/// use formal_algorithms::dynamic_array::DynamicArray;
///
/// let mut arr = DynamicArray::new();
/// arr.push(10);
/// arr.push(20);
/// assert_eq!(arr.len(), 2);
/// assert_eq!(arr.get(0), Some(&10));
/// assert_eq!(arr.pop(), Some(20));
/// ```
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct DynamicArray<T> {
    data: Vec<T>,
}

impl<T> Default for DynamicArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicArray<T> {
    /// 创建空动态数组，初始容量为 0
    pub fn new() -> Self {
        Self { data: Vec::new() }
    }

    /// 创建指定初始容量的动态数组
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::dynamic_array::DynamicArray;
    /// let arr: DynamicArray<i32> = DynamicArray::with_capacity(100);
    /// assert!(arr.capacity() >= 100);
    /// ```
    pub fn with_capacity(capacity: usize) -> Self {
        Self {
            data: Vec::with_capacity(capacity),
        }
    }

    /// 返回当前元素个数
    pub fn len(&self) -> usize {
        self.data.len()
    }

    /// 检查数组是否为空
    pub fn is_empty(&self) -> bool {
        self.data.is_empty()
    }

    /// 返回当前容量
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// 在尾部追加元素，O(1) 均摊
    ///
    /// 当 `len == capacity` 时触发扩容：新容量 = max(1, 2 * capacity)
    pub fn push(&mut self, value: T) {
        if self.data.len() == self.data.capacity() {
            let new_cap = if self.data.capacity() == 0 {
                1
            } else {
                self.data.capacity() * 2
            };
            self.data.reserve(new_cap - self.data.capacity());
        }
        self.data.push(value);
    }

    /// 移除尾部元素并返回，O(1) 均摊
    ///
    /// 当 `len <= capacity / 4` 时触发缩容：新容量 = max(1, capacity / 2)
    pub fn pop(&mut self) -> Option<T> {
        let result = self.data.pop();
        let cap = self.data.capacity();
        if cap > 1 && self.data.len() <= cap / 4 {
            self.data.shrink_to(std::cmp::max(cap / 2, 1));
        }
        result
    }

    /// 获取索引位置的不可变引用
    pub fn get(&self, index: usize) -> Option<&T> {
        self.data.get(index)
    }

    /// 获取索引位置的可变引用
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        self.data.get_mut(index)
    }

    /// 在指定位置插入元素，O(n)
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.data.len(), "index out of bounds");
        if self.data.len() == self.data.capacity() {
            let new_cap = if self.data.capacity() == 0 {
                1
            } else {
                self.data.capacity() * 2
            };
            self.data.reserve(new_cap - self.data.capacity());
        }
        self.data.insert(index, value);
    }

    /// 移除指定位置的元素，O(n)
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.data.len(), "index out of bounds");
        let value = self.data.remove(index);
        let cap = self.data.capacity();
        if cap > 1 && self.data.len() <= cap / 4 {
            self.data.shrink_to(std::cmp::max(cap / 2, 1));
        }
        value
    }

    /// 返回底层切片的不可变引用
    pub fn as_slice(&self) -> &[T] {
        &self.data
    }

    /// 返回底层切片的可变引用
    pub fn as_mut_slice(&mut self) -> &mut [T] {
        &mut self.data
    }
}

impl<T> From<Vec<T>> for DynamicArray<T> {
    fn from(vec: Vec<T>) -> Self {
        Self { data: vec }
    }
}

impl<T> From<DynamicArray<T>> for Vec<T> {
    fn from(arr: DynamicArray<T>) -> Vec<T> {
        arr.data
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_and_pop() {
        let mut arr = DynamicArray::new();
        assert_eq!(arr.pop(), None);
        arr.push(1);
        arr.push(2);
        arr.push(3);
        assert_eq!(arr.len(), 3);
        assert_eq!(arr.pop(), Some(3));
        assert_eq!(arr.pop(), Some(2));
        assert_eq!(arr.pop(), Some(1));
        assert_eq!(arr.pop(), None);
    }

    #[test]
    fn test_get_and_set() {
        let mut arr = DynamicArray::new();
        arr.push(10);
        arr.push(20);
        assert_eq!(arr.get(0), Some(&10));
        assert_eq!(arr.get(1), Some(&20));
        assert_eq!(arr.get(2), None);
        *arr.get_mut(1).unwrap() = 25;
        assert_eq!(arr.get(1), Some(&25));
    }

    #[test]
    fn test_insert_remove() {
        let mut arr = DynamicArray::new();
        arr.push(1);
        arr.push(3);
        arr.insert(1, 2);
        assert_eq!(arr.as_slice(), &[1, 2, 3]);
        assert_eq!(arr.remove(1), 2);
        assert_eq!(arr.as_slice(), &[1, 3]);
    }

    #[test]
    fn test_expand_and_contract() {
        let mut arr = DynamicArray::new();
        for i in 0..100 {
            arr.push(i);
        }
        assert_eq!(arr.len(), 100);
        for _ in 0..100 {
            arr.pop();
        }
        assert_eq!(arr.len(), 0);
        // 缩容后容量不应为 0（至少保留一定容量）
        assert!(arr.capacity() > 0);
    }

    #[test]
    fn test_drop() {
        let mut arr = DynamicArray::new();
        for i in 0..1000 {
            arr.push(vec![i]);
        }
        drop(arr);
        // 若 Drop 正确，此处不应发生堆损坏或双重释放
    }
}
