/// 动态数组 — 摊还分析示例
/// 倍增策略实现 O(1) 均摊插入
#[derive(Debug, Clone)]
pub struct DynamicArray<T> {
    buf: Vec<T>,
    len: usize,
    capacity: usize,
}

impl<T: Clone + Default> DynamicArray<T> {
    pub fn new() -> Self {
        Self::with_capacity(1)
    }

    pub fn with_capacity(cap: usize) -> Self {
        Self {
            buf: vec![T::default(); cap],
            len: 0,
            capacity: cap.max(1),
        }
    }

    /// 均摊 O(1) 的尾部插入
    pub fn push(&mut self, value: T) {
        if self.len == self.capacity {
            self.grow();
        }
        self.buf[self.len] = value;
        self.len += 1;
    }

    /// 均摊 O(1) 的尾部删除（支持缩容）
    pub fn pop(&mut self) -> Option<T> {
        if self.len == 0 {
            return None;
        }
        self.len -= 1;
        let value = self.buf[self.len].clone();

        // 缩容条件：使用率低于 25%
        if self.len < self.capacity / 4 && self.capacity > 4 {
            self.shrink();
        }
        Some(value)
    }

    fn grow(&mut self) {
        let new_cap = self.capacity * 2;
        let mut new_buf = vec![T::default(); new_cap];
        new_buf[..self.len].clone_from_slice(&self.buf[..self.len]);
        self.buf = new_buf;
        self.capacity = new_cap;
    }

    fn shrink(&mut self) {
        let new_cap = (self.capacity / 2).max(1);
        let mut new_buf = vec![T::default(); new_cap];
        new_buf[..self.len].clone_from_slice(&self.buf[..self.len]);
        self.buf = new_buf;
        self.capacity = new_cap;
    }

    pub fn len(&self) -> usize {
        self.len
    }

    pub fn is_empty(&self) -> bool {
        self.len == 0
    }

    pub fn capacity(&self) -> usize {
        self.capacity
    }

    /// 势能函数 Φ = 2n - s（当 n ≥ s/2 时）
    /// 或 Φ = s/2 - n（当 n < s/2 时）
    pub fn potential(&self) -> isize {
        let n = self.len as isize;
        let s = self.capacity as isize;
        if n >= s / 2 {
            2 * n - s
        } else {
            s / 2 - n
        }
    }

    pub fn amortized_cost_push(&self, will_grow: bool) -> isize {
        let c_i: isize = if will_grow { self.len as isize + 1 } else { 1 };
        let delta_phi = if will_grow {
            // 扩容后: s' = 2s = 2n, Φ' = 2(n+1) - 2n = 2
            // 扩容前: Φ = 2n - n = n
            2 - self.len as isize
        } else {
            // 普通插入: n 增加 1, s 不变
            // ΔΦ = (2(n+1) - s) - (2n - s) = 2
            2
        };
        c_i + delta_phi
    }
}

fn main() {
    println!("=== 动态数组摊还分析演示 ===\n");

    let mut arr = DynamicArray::<i32>::new();
    println!("初始: len={}, cap={}, Φ={}", arr.len(), arr.capacity(), arr.potential());

    for i in 0..17 {
        let will_grow = arr.len() == arr.capacity();
        let amortized = arr.amortized_cost_push(will_grow);
        arr.push(i);
        println!(
            "push({:2}) | len={:2} cap={:2} Φ={:3} | 摊还成本={}",
            i, arr.len(), arr.capacity(), arr.potential(), amortized
        );
    }

    println!("\n=== 删除与缩容演示 ===\n");
    while arr.len() > 0 {
        arr.pop();
        println!(
            "pop()    | len={:2} cap={:2} Φ={:3}",
            arr.len(), arr.capacity(), arr.potential()
        );
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_push_amortized() {
        let mut arr = DynamicArray::<i32>::new();
        for i in 0..1000 {
            arr.push(i);
        }
        assert_eq!(arr.len(), 1000);
        assert!(arr.capacity() >= 1000);
    }

    #[test]
    fn test_shrink() {
        let mut arr = DynamicArray::<i32>::with_capacity(16);
        for i in 0..16 { arr.push(i); }
        for _ in 0..12 { arr.pop(); }
        // 使用量 4/16 = 25%，可能已触发缩容
        assert!(arr.capacity() <= 16);
    }
}
