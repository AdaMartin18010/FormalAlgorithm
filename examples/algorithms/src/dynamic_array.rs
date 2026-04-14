//! # 动态数组 (Dynamic Array)
//!
//! 支持均摊 O(1) 尾部插入的自动扩容/缩容数组实现。
//!
//! ## 核心思想
//! - 当元素数量达到容量上限时，按一定 growth factor（通常为 2）扩容
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
    len: usize,
}

impl<T> Default for DynamicArray<T> {
    fn default() -> Self {
        Self::new()
    }
}

impl<T> DynamicArray<T> {
    /// 创建空动态数组，初始容量为 0
    pub fn new() -> Self {
        Self {
            data: Vec::new(),
            len: 0,
        }
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
            len: 0,
        }
    }

    /// 返回当前元素个数
    pub fn len(&self) -> usize {
        self.len
    }

    /// 检查数组是否为空
    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    /// 返回当前容量
    pub fn capacity(&self) -> usize {
        self.data.capacity()
    }

    /// 在尾部追加元素，O(1) 均摊
    ///
    /// 当 `len == capacity` 时触发扩容：新容量 = max(1, 2 * capacity)
    pub fn push(&mut self, value: T) {
        if self.len == self.data.capacity() {
            let new_cap = if self.data.capacity() == 0 {
                1
            } else {
                self.data.capacity() * 2
            };
            self.data.reserve(new_cap - self.data.capacity());
        }
        // SAFETY: len <= capacity, and reserve ensures capacity >= new_cap > len
        unsafe {
            let ptr = self.data.as_mut_ptr().add(self.len);
            std::ptr::write(ptr, value);
        }
        self.len += 1;
    }

    /// 移除尾部元素并返回，O(1) 均摊
    ///
    /// 当 `len <= capacity / 4` 时触发缩容：新容量 = max(1, capacity / 2)
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        // SAFETY: len was > 0, now points to valid initialized element
        let value = unsafe { std::ptr::read(self.data.as_ptr().add(self.len)) };

        let cap = self.data.capacity();
        if cap > 1 && self.len <= cap / 4 {
            self.shrink_to(std::cmp::max(cap / 2, 1));
        }
        Some(value)
    }

    /// 获取索引位置的不可变引用
    pub fn get(&self, index: usize) -> Option<&T> {
        if index < self.len {
            Some(unsafe { &*self.data.as_ptr().add(index) })
        } else {
            None
        }
    }

    /// 获取索引位置的可变引用
    pub fn get_mut(&mut self, index: usize) -> Option<&mut T> {
        if index < self.len {
            Some(unsafe { &mut *self.data.as_mut_ptr().add(index) })
        } else {
            None
        }
    }

    /// 在指定位置插入元素，O(n)
    pub fn insert(&mut self, index: usize, value: T) {
        assert!(index <= self.len, "index out of bounds");
        if self.len == self.data.capacity() {
            let new_cap = if self.data.capacity() == 0 {
                1
            } else {
                self.data.capacity() * 2
            };
            self.data.reserve(new_cap - self.data.capacity());
        }
        unsafe {
            let ptr = self.data.as_mut_ptr().add(index);
            std::ptr::copy(ptr, ptr.add(1), self.len - index);
            std::ptr::write(ptr, value);
        }
        self.len += 1;
    }

    /// 移除指定位置的元素，O(n)
    pub fn remove(&mut self, index: usize) -> T {
        assert!(index < self.len, "index out of bounds");
        unsafe {
            let ptr = self.data.as_mut_ptr().add(index);
            let value = std::ptr::read(ptr);
            std::ptr::copy(ptr.add(1), ptr, self.len - index - 1);
            self.len -= 1;
            value
        }
    }

    /// 收缩容量到指定值（不低于 len）
    fn shrink_to(&mut self, min_capacity: usize) {
        let new_cap = std::cmp::max(min_capacity, self.len);
        if new_cap < self.data.capacity() {
            let mut new_vec = Vec::with_capacity(new_cap);
            unsafe {
                std::ptr::copy_nonoverlapping(self.data.as_ptr(), new_vec.as_mut_ptr(), self.len);
                new_vec.set_len(self.len);
            }
            let old_cap = self.data.capacity();
            self.data = new_vec;
            // 显式释放旧内存（Vec drop 会自动处理）
            let _ = old_cap;
        }
    }
}

impl<T> Drop for DynamicArray<T> {
    fn drop(&mut self) {
        unsafe {
            std::ptr::drop_in_place(std::slice::from_raw_parts_mut(self.data.as_mut_ptr(), self.len));
        }
        self.len = 0;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_and_pop() {
        let mut arr = DynamicArray::new();
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
        *arr.get_mut(0).unwrap() = 100;
        assert_eq!(arr.get(0), Some(&100));
    }

    #[test]
    fn test_insert_remove() {
        let mut arr = DynamicArray::new();
        arr.push(1);
        arr.push(3);
        arr.insert(1, 2);
        assert_eq!(arr.get(0), Some(&1));
        assert_eq!(arr.get(1), Some(&2));
        assert_eq!(arr.get(2), Some(&3));
        assert_eq!(arr.remove(1), 2);
        assert_eq!(arr.get(1), Some(&3));
    }

    #[test]
    fn test_expand_and_contract() {
        let mut arr = DynamicArray::with_capacity(4);
        for i in 0..10 {
            arr.push(i);
        }
        assert!(arr.capacity() >= 10);
        for _ in 0..8 {
            arr.pop();
        }
        // After popping 8 elements, len=2, capacity should shrink
        assert!(arr.capacity() >= 2);
        assert!(arr.capacity() < 10);
    }

    #[test]
    fn test_drop() {
        let mut arr = DynamicArray::new();
        arr.push(String::from("hello"));
        arr.push(String::from("world"));
        drop(arr);
        // memory safely freed
    }
}
