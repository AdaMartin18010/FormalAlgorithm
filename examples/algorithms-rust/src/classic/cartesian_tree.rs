//! 笛卡尔树 (Cartesian Tree)
//! 
//! 性质:
//! - 堆性质: 父节点键值小于子节点
//! - 中序遍历为原序列
//! 应用: RMQ、LCA

pub struct CartesianTree {
    parent: Vec<usize>,
    left: Vec<usize>,
    right: Vec<usize>,
    root: usize,
}

impl CartesianTree {
    /// 构建笛卡尔树
    /// 
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn build(arr: &[i32]) -> Self {
        let n = arr.len();
        if n == 0 {
            return CartesianTree {
                parent: Vec::new(),
                left: Vec::new(),
                right: Vec::new(),
                root: 0,
            };
        }
        
        let mut parent = vec![usize::MAX; n];
        let mut left = vec![usize::MAX; n];
        let mut right = vec![usize::MAX; n];
        
        // 单调栈构建
        let mut stack: Vec<usize> = Vec::new();
        
        for i in 0..n {
            let mut last = usize::MAX;
            
            while let Some(&top) = stack.last() {
                if arr[top] > arr[i] {
                    last = top;
                    stack.pop();
                } else {
                    break;
                }
            }
            
            if let Some(&top) = stack.last() {
                right[top] = i;
                parent[i] = top;
            }
            
            if last != usize::MAX {
                left[i] = last;
                parent[last] = i;
            }
            
            stack.push(i);
        }
        
        // 根节点
        let root = parent.iter().position(|&p| p == usize::MAX).unwrap_or(0);
        
        CartesianTree { parent, left, right, root }
    }
    
    /// 获取根节点
    pub fn root(&self) -> usize {
        self.root
    }
    
    /// 获取父节点
    pub fn parent(&self, node: usize) -> Option<usize> {
        if node < self.parent.len() && self.parent[node] != usize::MAX {
            Some(self.parent[node])
        } else {
            None
        }
    }
    
    /// 获取左子节点
    pub fn left(&self, node: usize) -> Option<usize> {
        if node < self.left.len() && self.left[node] != usize::MAX {
            Some(self.left[node])
        } else {
            None
        }
    }
    
    /// 获取右子节点
    pub fn right(&self, node: usize) -> Option<usize> {
        if node < self.right.len() && self.right[node] != usize::MAX {
            Some(self.right[node])
        } else {
            None
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_cartesian_tree() {
        let arr = vec![3, 2, 4, 1, 5];
        let tree = CartesianTree::build(&arr);
        
        // 最小值1是根
        assert_eq!(tree.root(), 3);
        
        // 检查结构
        assert_eq!(tree.left(3), Some(1));  // 2是1的左子
        assert_eq!(tree.right(3), Some(4)); // 5是1的右子
    }
}
