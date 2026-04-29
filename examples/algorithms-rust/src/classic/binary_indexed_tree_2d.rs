//! 二维树状数组 (2D Binary Indexed Tree / Fenwick Tree)
//! 
//! 支持二维区间查询和单点更新
//! 时间复杂度: O(log n * log m)

pub struct BIT2D {
    tree: Vec<Vec<i64>>,
    n: usize,
    m: usize,
}

impl BIT2D {
    pub fn new(n: usize, m: usize) -> Self {
        BIT2D {
            tree: vec![vec![0; m + 1]; n + 1],
            n,
            m,
        }
    }
    
    fn lowbit(x: usize) -> usize {
        x & (!x + 1)
    }
    
    /// 单点更新: 在(x,y)位置增加delta
    pub fn update(&mut self, x: usize, y: usize, delta: i64) {
        let mut i = x;
        while i <= self.n {
            let mut j = y;
            while j <= self.m {
                self.tree[i][j] += delta;
                j += Self::lowbit(j);
            }
            i += Self::lowbit(i);
        }
    }
    
    /// 前缀和查询: (1,1)到(x,y)的和
    pub fn query(&self, x: usize, y: usize) -> i64 {
        let mut res = 0;
        let mut i = x;
        while i > 0 {
            let mut j = y;
            while j > 0 {
                res += self.tree[i][j];
                j -= Self::lowbit(j);
            }
            i -= Self::lowbit(i);
        }
        res
    }
    
    /// 子矩阵和查询: (x1,y1)到(x2,y2)的和
    pub fn range_query(&self, x1: usize, y1: usize, x2: usize, y2: usize) -> i64 {
        self.query(x2, y2) - self.query(x1 - 1, y2) 
            - self.query(x2, y1 - 1) + self.query(x1 - 1, y1 - 1)
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_bit2d() {
        let mut bit = BIT2D::new(5, 5);
        
        // 更新点
        bit.update(1, 1, 5);
        bit.update(2, 3, 7);
        bit.update(5, 5, 3);
        
        // 查询前缀和
        assert_eq!(bit.query(1, 1), 5);
        assert_eq!(bit.query(2, 3), 12);
        
        // 查询子矩阵
        assert_eq!(bit.range_query(1, 1, 2, 3), 12);
    }
}
