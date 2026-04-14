//! van Emde Boas 树 (van Emde Boas Tree)
//!
//! 一种支持前驱/后继查询的递归数据结构，所有操作的时间复杂度均为 O(log log u)。
//! 基于《算法导论》(CLRS) 第20章实现。
//!
//! # 核心特性
//! - 键值为非负整数，范围在 [0, u-1]
//! - universe size u 必须是 2 的幂（若不是则自动向上取整到最近的 2 的幂）
//! - `min` 与 `max` 直接存储在当前节点，不递归存入子 cluster
//!
//! # 复杂度
//! | 操作 | 时间复杂度 | 空间复杂度 |
//! |------|-----------|-----------|
//! | insert | O(log log u) | O(u) |
//! | delete | O(log log u) | O(u) |
//! | member | O(log log u) | O(u) |
//! | minimum | O(1) | O(u) |
//! | maximum | O(1) | O(u) |
//! | successor | O(log log u) | O(u) |
//! | predecessor | O(log log u) | O(u) |

/// van Emde Boas 树节点
#[derive(Debug)]
struct VebNode {
    /// 当前节点的 universe size
    u: usize,
    /// 当前集合中的最小元素（不递归存储在 cluster 中）
    min: Option<usize>,
    /// 当前集合中的最大元素（不递归存储在 cluster 中）
    max: Option<usize>,
    /// 记录哪些 cluster 非空的 summary 树
    summary: Option<Box<VebNode>>,
    /// cluster 数组，每个元素对应一个子 vEB 树
    cluster: Vec<Option<Box<VebNode>>>,
}

impl VebNode {
    /// 创建指定 universe size 的节点
    fn new(u: usize) -> Self {
        assert!(
            u >= 2 && u.is_power_of_two(),
            "universe size 必须是大于等于 2 的 2 的幂"
        );
        if u == 2 {
            VebNode {
                u,
                min: None,
                max: None,
                summary: None,
                cluster: Vec::new(),
            }
        } else {
            let upper = upper_sqrt(u);
            let lower = lower_sqrt(u);
            let summary = Some(Box::new(VebNode::new(upper)));
            let cluster = (0..upper)
                .map(|_| Some(Box::new(VebNode::new(lower))))
                .collect();
            VebNode {
                u,
                min: None,
                max: None,
                summary,
                cluster,
            }
        }
    }

    #[inline]
    fn lower(&self) -> usize {
        lower_sqrt(self.u)
    }

    #[inline]
    fn high(&self, x: usize) -> usize {
        x / self.lower()
    }

    #[inline]
    fn low(&self, x: usize) -> usize {
        x % self.lower()
    }

    #[inline]
    fn index(&self, high: usize, low: usize) -> usize {
        high * self.lower() + low
    }

    fn insert(&mut self, x: usize) {
        assert!(x < self.u, "key {} 超出 universe 范围 [0, {})", x, self.u);
        if self.min.is_none() {
            self.min = Some(x);
            self.max = Some(x);
            return;
        }

        let mut x = x;
        if let Some(min) = self.min {
            if x < min {
                std::mem::swap(&mut x, self.min.as_mut().unwrap());
            }
        }

        // 重复插入最小值，直接忽略
        if x == self.min.unwrap() {
            return;
        }

        if self.u > 2 {
            let high = self.high(x);
            let low = self.low(x);
            let cluster = self.cluster[high].as_mut().unwrap();
            if cluster.min.is_none() {
                self.summary.as_mut().unwrap().insert(high);
                cluster.min = Some(low);
                cluster.max = Some(low);
            } else {
                cluster.insert(low);
            }
        }

        if x > self.max.unwrap() {
            self.max = Some(x);
        }
    }

    fn delete(&mut self, x: usize) {
        assert!(x < self.u, "key {} 超出 universe 范围 [0, {})", x, self.u);
        if !self.member(x) {
            return;
        }

        if self.min == self.max {
            self.min = None;
            self.max = None;
            return;
        }

        if self.u == 2 {
            self.min = Some(1 - x);
            self.max = self.min;
            return;
        }

        let mut x = x;
        if x == self.min.unwrap() {
            let first_cluster = self.summary.as_ref().unwrap().min.unwrap();
            let cluster_min = self.cluster[first_cluster].as_ref().unwrap().min.unwrap();
            x = self.index(first_cluster, cluster_min);
            self.min = Some(x);
        }

        let high = self.high(x);
        let low = self.low(x);
        self.cluster[high].as_mut().unwrap().delete(low);

        if self.cluster[high].as_ref().unwrap().min.is_none() {
            self.summary.as_mut().unwrap().delete(high);
            if x == self.max.unwrap() {
                let summary_max = self.summary.as_ref().unwrap().max;
                if let Some(sm) = summary_max {
                    let cluster_max = self.cluster[sm].as_ref().unwrap().max.unwrap();
                    self.max = Some(self.index(sm, cluster_max));
                } else {
                    self.max = self.min;
                }
            }
        } else if x == self.max.unwrap() {
            let cluster_max = self.cluster[high].as_ref().unwrap().max.unwrap();
            self.max = Some(self.index(high, cluster_max));
        }
    }

    fn member(&self, x: usize) -> bool {
        assert!(x < self.u, "key {} 超出 universe 范围 [0, {})", x, self.u);
        if self.min == Some(x) || self.max == Some(x) {
            return true;
        }
        if self.u == 2 {
            false
        } else {
            let high = self.high(x);
            let low = self.low(x);
            self.cluster[high].as_ref().unwrap().member(low)
        }
    }

    fn minimum(&self) -> Option<usize> {
        self.min
    }

    fn maximum(&self) -> Option<usize> {
        self.max
    }

    fn successor(&self, x: usize) -> Option<usize> {
        assert!(x < self.u, "key {} 超出 universe 范围 [0, {})", x, self.u);
        if self.u == 2 {
            if x == 0 && self.max == Some(1) {
                Some(1)
            } else {
                None
            }
        } else if let Some(min) = self.min {
            if x < min {
                Some(min)
            } else {
                let high = self.high(x);
                let low = self.low(x);
                let cluster = self.cluster[high].as_ref().unwrap();
                if let Some(max_low) = cluster.max {
                    if low < max_low {
                        let offset = cluster.successor(low).unwrap();
                        return Some(self.index(high, offset));
                    }
                }
                self.summary.as_ref().unwrap().successor(high).map(|sc| {
                    let offset = self.cluster[sc].as_ref().unwrap().min.unwrap();
                    self.index(sc, offset)
                })
            }
        } else {
            None
        }
    }

    fn predecessor(&self, x: usize) -> Option<usize> {
        assert!(x < self.u, "key {} 超出 universe 范围 [0, {})", x, self.u);
        if self.u == 2 {
            if x == 1 && self.min == Some(0) {
                Some(0)
            } else {
                None
            }
        } else if let Some(max) = self.max {
            if x > max {
                Some(max)
            } else {
                let high = self.high(x);
                let low = self.low(x);
                let cluster = self.cluster[high].as_ref().unwrap();
                if let Some(min_low) = cluster.min {
                    if low > min_low {
                        let offset = cluster.predecessor(low).unwrap();
                        return Some(self.index(high, offset));
                    }
                }
                if let Some(pred_cluster) = self.summary.as_ref().unwrap().predecessor(high) {
                    let offset = self.cluster[pred_cluster].as_ref().unwrap().max.unwrap();
                    Some(self.index(pred_cluster, offset))
                } else {
                    self.min.filter(|&m| x > m)
                }
            }
        } else {
            None
        }
    }
}

#[inline]
fn lower_sqrt(u: usize) -> usize {
    let k = u.trailing_zeros() as usize;
    1usize << (k / 2)
}

#[inline]
fn upper_sqrt(u: usize) -> usize {
    let k = u.trailing_zeros() as usize;
    1usize << ((k + 1) / 2)
}

/// van Emde Boas 树
///
/// 提供 O(log log u) 时间复杂度的插入、删除、成员查询、前驱与后继操作。
#[derive(Debug)]
pub struct VanEmdeBoasTree {
    root: VebNode,
}

impl VanEmdeBoasTree {
    /// 创建一个新的 vEB 树
    ///
    /// 如果传入的 `universe_size` 不是 2 的幂，则会自动向上取整到最近的 2 的幂（最小为 2）。
    ///
    /// # 复杂度
    /// - 时间: O(u)
    /// - 空间: O(u)
    pub fn new(universe_size: usize) -> Self {
        let u = universe_size.max(2).next_power_of_two();
        VanEmdeBoasTree {
            root: VebNode::new(u),
        }
    }

    /// 插入元素 x
    ///
    /// # 复杂度: O(log log u)
    pub fn insert(&mut self, x: usize) {
        self.root.insert(x);
    }

    /// 删除元素 x
    ///
    /// # 复杂度: O(log log u)
    pub fn delete(&mut self, x: usize) {
        self.root.delete(x);
    }

    /// 判断 x 是否为集合成员
    ///
    /// # 复杂度: O(log log u)
    pub fn member(&self, x: usize) -> bool {
        self.root.member(x)
    }

    /// 返回集合中的最小元素
    ///
    /// # 复杂度: O(1)
    pub fn minimum(&self) -> Option<usize> {
        self.root.minimum()
    }

    /// 返回集合中的最大元素
    ///
    /// # 复杂度: O(1)
    pub fn maximum(&self) -> Option<usize> {
        self.root.maximum()
    }

    /// 返回 x 的后继（大于 x 的最小元素）
    ///
    /// # 复杂度: O(log log u)
    pub fn successor(&self, x: usize) -> Option<usize> {
        self.root.successor(x)
    }

    /// 返回 x 的前驱（小于 x 的最大元素）
    ///
    /// # 复杂度: O(log log u)
    pub fn predecessor(&self, x: usize) -> Option<usize> {
        self.root.predecessor(x)
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_empty_tree() {
        let tree = VanEmdeBoasTree::new(2);
        assert!(!tree.member(0));
        assert_eq!(tree.minimum(), None);
        assert_eq!(tree.maximum(), None);
        assert_eq!(tree.successor(0), None);
        assert_eq!(tree.predecessor(0), None);
    }

    #[test]
    fn test_universe_size_2() {
        let mut tree = VanEmdeBoasTree::new(2);
        tree.insert(0);
        tree.insert(1);
        assert!(tree.member(0));
        assert!(tree.member(1));
        assert_eq!(tree.minimum(), Some(0));
        assert_eq!(tree.maximum(), Some(1));
        assert_eq!(tree.successor(0), Some(1));
        assert_eq!(tree.successor(1), None);
        assert_eq!(tree.predecessor(0), None);
        assert_eq!(tree.predecessor(1), Some(0));

        tree.delete(0);
        assert!(!tree.member(0));
        assert_eq!(tree.minimum(), Some(1));
        assert_eq!(tree.maximum(), Some(1));

        tree.delete(1);
        assert_eq!(tree.minimum(), None);
        assert_eq!(tree.maximum(), None);
    }

    #[test]
    fn test_universe_size_4() {
        let mut tree = VanEmdeBoasTree::new(4);
        tree.insert(1);
        tree.insert(3);
        assert!(tree.member(1));
        assert!(tree.member(3));
        assert!(!tree.member(0));
        assert!(!tree.member(2));
        assert_eq!(tree.minimum(), Some(1));
        assert_eq!(tree.maximum(), Some(3));

        assert_eq!(tree.successor(0), Some(1));
        assert_eq!(tree.successor(1), Some(3));
        assert_eq!(tree.successor(2), Some(3));
        assert_eq!(tree.successor(3), None);

        assert_eq!(tree.predecessor(1), None);
        assert_eq!(tree.predecessor(2), Some(1));
        assert_eq!(tree.predecessor(3), Some(1));

        tree.delete(1);
        assert!(!tree.member(1));
        assert_eq!(tree.minimum(), Some(3));
        assert_eq!(tree.maximum(), Some(3));

        tree.delete(3);
        assert_eq!(tree.minimum(), None);
        assert_eq!(tree.maximum(), None);
    }

    #[test]
    fn test_universe_size_16() {
        let mut tree = VanEmdeBoasTree::new(16);
        let values = [2, 3, 5, 7, 11, 13];
        for &v in &values {
            tree.insert(v);
        }

        assert_eq!(tree.minimum(), Some(2));
        assert_eq!(tree.maximum(), Some(13));

        // successor chain
        assert_eq!(tree.successor(0), Some(2));
        assert_eq!(tree.successor(2), Some(3));
        assert_eq!(tree.successor(3), Some(5));
        assert_eq!(tree.successor(5), Some(7));
        assert_eq!(tree.successor(7), Some(11));
        assert_eq!(tree.successor(11), Some(13));
        assert_eq!(tree.successor(13), None);

        // predecessor chain
        assert_eq!(tree.predecessor(14), Some(13));
        assert_eq!(tree.predecessor(13), Some(11));
        assert_eq!(tree.predecessor(12), Some(11));
        assert_eq!(tree.predecessor(11), Some(7));
        assert_eq!(tree.predecessor(6), Some(5));
        assert_eq!(tree.predecessor(5), Some(3));
        assert_eq!(tree.predecessor(3), Some(2));
        assert_eq!(tree.predecessor(2), None);

        // delete min
        tree.delete(2);
        assert!(!tree.member(2));
        assert_eq!(tree.minimum(), Some(3));

        // delete max
        tree.delete(13);
        assert!(!tree.member(13));
        assert_eq!(tree.maximum(), Some(11));

        // delete intermediate
        tree.delete(7);
        assert!(!tree.member(7));
        assert_eq!(tree.successor(5), Some(11));
        assert_eq!(tree.predecessor(11), Some(5));
    }

    #[test]
    fn test_universe_size_64() {
        let mut tree = VanEmdeBoasTree::new(64);
        let values = [0, 5, 10, 15, 20, 31, 32, 48, 63];
        for &v in &values {
            tree.insert(v);
        }

        for &v in &values {
            assert!(tree.member(v));
        }

        assert_eq!(tree.minimum(), Some(0));
        assert_eq!(tree.maximum(), Some(63));

        assert_eq!(tree.successor(0), Some(5));
        assert_eq!(tree.successor(5), Some(10));
        assert_eq!(tree.successor(31), Some(32));
        assert_eq!(tree.successor(48), Some(63));
        assert_eq!(tree.successor(63), None);

        assert_eq!(tree.predecessor(63), Some(48));
        assert_eq!(tree.predecessor(48), Some(32));
        assert_eq!(tree.predecessor(32), Some(31));
        assert_eq!(tree.predecessor(5), Some(0));
        assert_eq!(tree.predecessor(0), None);

        // delete all
        for &v in &values {
            tree.delete(v);
        }
        assert_eq!(tree.minimum(), None);
        assert_eq!(tree.maximum(), None);
    }

    #[test]
    fn test_duplicate_insert() {
        let mut tree = VanEmdeBoasTree::new(16);
        tree.insert(5);
        tree.insert(5);
        assert!(tree.member(5));
        tree.delete(5);
        assert!(!tree.member(5));
    }

    #[test]
    fn test_delete_nonexistent() {
        let mut tree = VanEmdeBoasTree::new(16);
        tree.insert(3);
        tree.delete(5); // no-op
        assert!(tree.member(3));
        assert_eq!(tree.minimum(), Some(3));
    }

    #[test]
    fn test_round_up_universe_size() {
        let mut tree = VanEmdeBoasTree::new(5);
        // universe size rounded up to 8
        tree.insert(7);
        assert!(tree.member(7));
        assert_eq!(tree.maximum(), Some(7));
    }

    #[test]
    #[should_panic(expected = "超出 universe 范围")]
    fn test_out_of_bounds() {
        let tree = VanEmdeBoasTree::new(4);
        tree.member(4);
    }
}
