//! 线段树 (Segment Tree)
//! 
//! 支持区间查询和单点更新的高效数据结构
//! 
//! 对标: MIT 6.006 / Stanford CS161

/// 线段树节点
#[derive(Clone, Debug)]
pub struct SegmentTree<T> {
    /// 线段树数组 (4倍原数组大小)
    tree: Vec<T>,
    /// 原数组大小
    n: usize,
    /// 单位元 (用于查询的初始值)
    identity: T,
    /// 合并操作
    merge: fn(T, T) -> T,
}

impl<T: Clone + Copy + Default> SegmentTree<T> {
    /// 构建线段树
    /// 
    /// # 参数
    /// - `data`: 初始数组
    /// - `identity`: 单位元 (如求和时为0，求最值时为∞)
    /// - `merge`: 合并操作 (如|a+b|, |max(a,b)|等)
    /// 
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(4n)
    pub fn new(data: &[T], identity: T, merge: fn(T, T) -> T) -> Self {
        let n = data.len();
        let tree = vec![identity; 4 * n];
        let mut seg_tree = SegmentTree { tree, n, identity, merge };
        
        if n > 0 {
            seg_tree.build(0, 0, n - 1, data);
        }
        
        seg_tree
    }
    
    /// 递归构建
    fn build(&mut self, node: usize, left: usize, right: usize, data: &[T]) {
        if left == right {
            self.tree[node] = data[left];
            return;
        }
        
        let mid = (left + right) / 2;
        let left_child = 2 * node + 1;
        let right_child = 2 * node + 2;
        
        self.build(left_child, left, mid, data);
        self.build(right_child, mid + 1, right, data);
        
        self.tree[node] = (self.merge)(self.tree[left_child], self.tree[right_child]);
    }
    
    /// 单点更新
    /// 
    /// # 复杂度: O(log n)
    pub fn update(&mut self, index: usize, value: T) {
        self.update_recursive(0, 0, self.n - 1, index, value);
    }
    
    fn update_recursive(&mut self, node: usize, left: usize, right: usize, index: usize, value: T) {
        if left == right {
            self.tree[node] = value;
            return;
        }
        
        let mid = (left + right) / 2;
        let left_child = 2 * node + 1;
        let right_child = 2 * node + 2;
        
        if index <= mid {
            self.update_recursive(left_child, left, mid, index, value);
        } else {
            self.update_recursive(right_child, mid + 1, right, index, value);
        }
        
        self.tree[node] = (self.merge)(self.tree[left_child], self.tree[right_child]);
    }
    
    /// 区间查询
    /// 
    /// # 复杂度: O(log n)
    pub fn query(&self, query_left: usize, query_right: usize) -> T {
        if self.n == 0 || query_left > query_right {
            return self.identity;
        }
        self.query_recursive(0, 0, self.n - 1, query_left, query_right)
    }
    
    fn query_recursive(&self, node: usize, left: usize, right: usize, ql: usize, qr: usize) -> T {
        // 完全包含
        if ql <= left && right <= qr {
            return self.tree[node];
        }
        
        // 无交集
        if right < ql || left > qr {
            return self.identity;
        }
        
        let mid = (left + right) / 2;
        let left_child = 2 * node + 1;
        let right_child = 2 * node + 2;
        
        let left_val = self.query_recursive(left_child, left, mid, ql, qr);
        let right_val = self.query_recursive(right_child, mid + 1, right, ql, qr);
        
        (self.merge)(left_val, right_val)
    }
}

/// 支持懒标记的线段树 (区间更新)
pub struct LazySegmentTree {
    tree: Vec<i64>,
    lazy: Vec<i64>,
    n: usize,
}

impl LazySegmentTree {
    pub fn new(n: usize) -> Self {
        LazySegmentTree {
            tree: vec![0; 4 * n],
            lazy: vec![0; 4 * n],
            n,
        }
    }
    
    /// 区间加值更新
    /// 
    /// # 复杂度: O(log n)
    pub fn range_add(&mut self, left: usize, right: usize, value: i64) {
        self.range_add_recursive(1, 0, self.n - 1, left, right, value);
    }
    
    fn range_add_recursive(&mut self, node: usize, nl: usize, nr: usize, 
                          left: usize, right: usize, value: i64) {
        // 下传懒标记
        self.push_down(node, nl, nr);
        
        if left > nr || right < nl {
            return;
        }
        
        if left <= nl && nr <= right {
            self.tree[node] += value * (nr - nl + 1) as i64;
            if nl != nr {
                self.lazy[node] += value;
            }
            return;
        }
        
        let mid = (nl + nr) / 2;
        self.range_add_recursive(node * 2, nl, mid, left, right, value);
        self.range_add_recursive(node * 2 + 1, mid + 1, nr, left, right, value);
        
        self.tree[node] = self.tree[node * 2] + self.tree[node * 2 + 1];
    }
    
    /// 区间求和查询
    /// 
    /// # 复杂度: O(log n)
    pub fn range_sum(&mut self, left: usize, right: usize) -> i64 {
        self.range_sum_recursive(1, 0, self.n - 1, left, right)
    }
    
    fn range_sum_recursive(&mut self, node: usize, nl: usize, nr: usize,
                          left: usize, right: usize) -> i64 {
        self.push_down(node, nl, nr);
        
        if left > nr || right < nl {
            return 0;
        }
        
        if left <= nl && nr <= right {
            return self.tree[node];
        }
        
        let mid = (nl + nr) / 2;
        let left_sum = self.range_sum_recursive(node * 2, nl, mid, left, right);
        let right_sum = self.range_sum_recursive(node * 2 + 1, mid + 1, nr, left, right);
        
        left_sum + right_sum
    }
    
    fn push_down(&mut self, node: usize, nl: usize, nr: usize) {
        if self.lazy[node] != 0 && nl != nr {
            let mid = (nl + nr) / 2;
            let left_len = (mid - nl + 1) as i64;
            let right_len = (nr - mid) as i64;
            
            self.tree[node * 2] += self.lazy[node] * left_len;
            self.tree[node * 2 + 1] += self.lazy[node] * right_len;
            
            self.lazy[node * 2] += self.lazy[node];
            self.lazy[node * 2 + 1] += self.lazy[node];
            
            self.lazy[node] = 0;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_sum_segment_tree() {
        let data = vec![1, 3, 5, 7, 9, 11];
        let mut seg_tree = SegmentTree::new(&data, 0, |a, b| a + b);
        
        // 查询区间和
        assert_eq!(seg_tree.query(0, 2), 9);   // 1+3+5
        assert_eq!(seg_tree.query(1, 4), 24);  // 3+5+7+9
        assert_eq!(seg_tree.query(0, 5), 36);  // 总和
        
        // 更新
        seg_tree.update(2, 10);  // 5 -> 10
        assert_eq!(seg_tree.query(0, 2), 14);  // 1+3+10
        assert_eq!(seg_tree.query(0, 5), 41);  // 新总和
    }
    
    #[test]
    fn test_min_segment_tree() {
        let data = vec![5, 2, 8, 1, 9, 3];
        let mut seg_tree = SegmentTree::new(&data, i32::MAX, |a, b| a.min(b));
        
        assert_eq!(seg_tree.query(0, 2), 2);  // min(5,2,8)
        assert_eq!(seg_tree.query(3, 5), 1);  // min(1,9,3)
        assert_eq!(seg_tree.query(0, 5), 1);  // 全局最小
        
        seg_tree.update(3, 0);
        assert_eq!(seg_tree.query(0, 5), 0);
    }
    
    #[test]
    fn test_lazy_segment_tree() {
        let mut lazy_st = LazySegmentTree::new(10);
        
        // 初始全为0
        assert_eq!(lazy_st.range_sum(0, 9), 0);
        
        // 区间加
        lazy_st.range_add(0, 4, 5);  // [0,4]加5
        assert_eq!(lazy_st.range_sum(0, 4), 25);  // 5*5
        assert_eq!(lazy_st.range_sum(5, 9), 0);   // 未改变
        
        lazy_st.range_add(3, 7, 3);  // [3,7]加3
        // [0,2]=5, [3,4]=8, [5,7]=3, [8,9]=0
        assert_eq!(lazy_st.range_sum(0, 9), 5*3 + 8*2 + 3*3);  // 15+16+9=40
    }
}
