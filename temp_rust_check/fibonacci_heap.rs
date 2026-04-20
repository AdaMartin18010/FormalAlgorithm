use std::ptr::NonNull;

/// 斐波那契堆节点
pub struct FibNode<K: Ord + Clone, V: Clone> {
    key: K,
    val: V,
    degree: usize,
    marked: bool,
    parent: Option<NonNull<FibNode<K, V>>>,
    child: Option<NonNull<FibNode<K, V>>>,
    left: Option<NonNull<FibNode<K, V>>>,
    right: Option<NonNull<FibNode<K, V>>>,
}

/// 斐波那契堆
/// INSERT / UNION: O(1) 摊还
/// EXTRACT-MIN: O(log n) 摊还
/// DECREASE-KEY: O(1) 摊还
pub struct FibonacciHeap<K: Ord + Clone, V: Clone> {
    min: Option<NonNull<FibNode<K, V>>>,
    n: usize,      // 总节点数
    t: usize,      // 根表树数量（用于势能分析）
    m: usize,      // 标记节点数（用于势能分析）
}

impl<K: Ord + Clone, V: Clone> FibonacciHeap<K, V> {
    pub fn new() -> Self {
        Self { min: None, n: 0, t: 0, m: 0 }
    }

    pub fn is_empty(&self) -> bool {
        self.min.is_none()
    }

    pub fn len(&self) -> usize {
        self.n
    }

    /// INSERT — O(1) 实际 / 摊还
    pub fn insert(&mut self, key: K, val: V) {
        let node = Box::new(FibNode {
            key: key.clone(), val,
            degree: 0, marked: false,
            parent: None, child: None,
            left: None, right: None,
        });
        let ptr = NonNull::new(Box::into_raw(node));

        if let Some(min) = self.min {
            unsafe {
                // 插入根表双链表
                let left = (*min.as_ptr()).left;
                (*min.as_ptr()).left = ptr;
                (*ptr.unwrap().as_ptr()).right = Some(min);
                (*ptr.unwrap().as_ptr()).left = left;
                if let Some(l) = left {
                    (*l.as_ptr()).right = ptr;
                }
                if key < (*min.as_ptr()).key {
                    self.min = ptr;
                }
            }
        } else {
            self.min = ptr;
            unsafe {
                (*ptr.unwrap().as_ptr()).left = ptr;
                (*ptr.unwrap().as_ptr()).right = ptr;
            }
        }
        self.n += 1;
        self.t += 1;
    }

    /// UNION — O(1) 实际 / 摊还
    pub fn union(&mut self, other: &mut Self) {
        if other.is_empty() { return; }
        if self.is_empty() {
            *self = std::mem::replace(other, Self::new());
            return;
        }

        unsafe {
            let self_min = self.min.unwrap();
            let other_min = other.min.unwrap();
            let self_right = (*self_min.as_ptr()).right;
            let other_left = (*other_min.as_ptr()).left;

            (*self_min.as_ptr()).right = Some(other_min);
            (*other_min.as_ptr()).left = Some(self_min);
            if let Some(sr) = self_right {
                (*sr.as_ptr()).left = other_left;
            }
            if let Some(ol) = other_left {
                (*ol.as_ptr()).right = self_right;
            }

            if (*other_min.as_ptr()).key < (*self_min.as_ptr()).key {
                self.min = Some(other_min);
            }
        }
        self.n += other.n;
        self.t += other.t;
        self.m += other.m;
        other.n = 0;
        other.t = 0;
        other.m = 0;
        other.min = None;
    }

    /// MINIMUM — O(1) 实际
    pub fn minimum(&self) -> Option<(K, V)> {
        self.min.map(|m| unsafe {
            ((*m.as_ptr()).key.clone(), (*m.as_ptr()).val.clone())
        })
    }

    /// EXTRACT-MIN — O(log n) 摊还
    pub fn extract_min(&mut self) -> Option<(K, V)> {
        let z = self.min?;
        unsafe {
            // 将 z 的所有子节点加入根表
            if let Some(child) = (*z.as_ptr()).child {
                let mut c = child;
                loop {
                    (*c.as_ptr()).parent = None;
                    if let Some(next) = (*c.as_ptr()).right {
                        c = next;
                        if c == child { break; }
                    } else { break; }
                }
            }

            let key = (*z.as_ptr()).key.clone();
            let val = (*z.as_ptr()).val.clone();

            // 从根表移除 z
            let left = (*z.as_ptr()).left;
            let right = (*z.as_ptr()).right;
            if let Some(l) = left { (*l.as_ptr()).right = right; }
            if let Some(r) = right { (*r.as_ptr()).left = left; }

            if right == Some(z) {
                self.min = None;
            } else {
                self.min = right;
                self.consolidate();
            }
            self.n -= 1;
            self.t = self.t.saturating_sub(1);
            drop(Box::from_raw(z.as_ptr()));
            Some((key, val))
        }
    }

    fn consolidate(&mut self) {
        if self.min.is_none() { return; }
        let max_degree = (self.n as f64).log2() as usize + 2;
        let mut aux: Vec<Option<NonNull<FibNode<K, V>>>> = vec![None; max_degree];

        // 收集根表节点
        let mut roots = vec![];
        if let Some(min) = self.min {
            unsafe {
                let mut curr = min;
                loop {
                    roots.push(curr);
                    if let Some(r) = (*curr.as_ptr()).right {
                        curr = r;
                        if curr == min { break; }
                    } else { break; }
                }
            }
        }

        for mut w in roots {
            let mut d = unsafe { (*w.as_ptr()).degree };
            while let Some(mut y) = aux[d] {
                if unsafe { (*w.as_ptr()).key > (*y.as_ptr()).key } {
                    std::mem::swap(&mut w, &mut y);
                }
                self.link(y, w);
                aux[d] = None;
                d += 1;
            }
            aux[d] = Some(w);
        }

        self.min = None;
        self.t = 0;
        for node in aux.into_iter().flatten() {
            if self.min.is_none() {
                self.min = Some(node);
                unsafe {
                    (*node.as_ptr()).left = Some(node);
                    (*node.as_ptr()).right = Some(node);
                }
            } else {
                unsafe {
                    let min_ptr = self.min.unwrap();
                    let left = (*min_ptr.as_ptr()).left;
                    (*min_ptr.as_ptr()).left = Some(node);
                    (*node.as_ptr()).right = Some(min_ptr);
                    (*node.as_ptr()).left = left;
                    if let Some(l) = left {
                        (*l.as_ptr()).right = Some(node);
                    }
                    if (*node.as_ptr()).key < (*min_ptr.as_ptr()).key {
                        self.min = Some(node);
                    }
                }
            }
            self.t += 1;
        }
    }

    fn link(&mut self, y: NonNull<FibNode<K, V>>, x: NonNull<FibNode<K, V>>) {
        unsafe {
            // 从根表移除 y
            let yl = (*y.as_ptr()).left;
            let yr = (*y.as_ptr()).right;
            if let Some(l) = yl { (*l.as_ptr()).right = yr; }
            if let Some(r) = yr { (*r.as_ptr()).left = yl; }

            (*y.as_ptr()).parent = Some(x);
            (*y.as_ptr()).marked = false;

            if let Some(child) = (*x.as_ptr()).child {
                let left = (*child.as_ptr()).left;
                (*child.as_ptr()).left = Some(y);
                (*y.as_ptr()).right = Some(child);
                (*y.as_ptr()).left = left;
                if let Some(l) = left {
                    (*l.as_ptr()).right = Some(y);
                }
            } else {
                (*x.as_ptr()).child = Some(y);
                (*y.as_ptr()).left = Some(y);
                (*y.as_ptr()).right = Some(y);
            }
            (*x.as_ptr()).degree += 1;
        }
    }

    /// 势能函数 Φ = t(H) + 2·m(H)
    pub fn potential(&self) -> usize {
        self.t + 2 * self.m
    }
}

fn main() {
    println!("=== 斐波那契堆摊还分析演示 ===\n");

    let mut heap = FibonacciHeap::<i32, &str>::new();
    println!("操作: 插入 5 个元素");
    for (k, v) in [(3, "C"), (1, "A"), (4, "D"), (2, "B"), (5, "E")] {
        heap.insert(k, v);
        println!("  insert({}, {}) | n={} t={} m={} Φ={}", k, v, heap.len(), heap.t, heap.m, heap.potential());
    }

    println!("\n操作: extract_min");
    while let Some((k, v)) = heap.extract_min() {
        println!("  extract_min → ({}, {}) | n={} t={} m={} Φ={}", k, v, heap.len(), heap.t, heap.m, heap.potential());
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_insert_and_extract() {
        let mut heap = FibonacciHeap::new();
        heap.insert(3, "c");
        heap.insert(1, "a");
        heap.insert(2, "b");
        assert_eq!(heap.extract_min(), Some((1, "a")));
        assert_eq!(heap.extract_min(), Some((2, "b")));
        assert_eq!(heap.extract_min(), Some((3, "c")));
    }

    #[test]
    fn test_union() {
        let mut h1 = FibonacciHeap::new();
        h1.insert(1, "a");
        let mut h2 = FibonacciHeap::new();
        h2.insert(2, "b");
        h1.union(&mut h2);
        assert_eq!(h1.extract_min(), Some((1, "a")));
        assert_eq!(h1.extract_min(), Some((2, "b")));
    }
}
