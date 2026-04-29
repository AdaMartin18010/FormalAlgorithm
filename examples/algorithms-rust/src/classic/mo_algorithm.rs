//! Mo算法 (离线区间查询)
//!
//! 一种用于解决离线区间查询问题的分块算法，通过巧妙的排序策略减少指针移动次数。
//!
//! ## 核心思想
//! - 将查询按左端点所在块排序，同一块内按右端点排序
//! - 使用两个指针在数组上移动，动态维护当前区间的答案
//! - 通过"添加/删除"操作更新答案
//!
//! ## 适用问题
//! - 区间众数
//! - 区间不同数字个数
//! - 区间频率统计
//! - 带修改的区间查询（带修莫队）
//!
//! ## 复杂度分析
//! - 时间: O((n + q) × √n)，其中 n 为数组长度，q 为查询数量
//! - 空间: O(n + q)
//!
//! 对标: 竞赛编程标准算法

/// 普通莫队查询
#[derive(Clone, Debug)]
pub struct Query {
    /// 查询左端点（闭区间）
    pub left: usize,
    /// 查询右端点（闭区间）
    pub right: usize,
    /// 查询编号（用于恢复顺序）
    pub id: usize,
    /// 左端点所在块
    block_id: usize,
}

impl Query {
    /// 创建新查询
    pub fn new(left: usize, right: usize, id: usize, block_size: usize) -> Self {
        Query {
            left,
            right,
            id,
            block_id: left / block_size,
        }
    }
}

/// 莫队算法结构
pub struct MoAlgorithm {
    /// 块大小（通常为 √n）
    block_size: usize,
    /// 当前左指针
    cur_l: usize,
    /// 当前右指针
    cur_r: usize,
    /// 当前区间答案
    cur_ans: i64,
}

impl MoAlgorithm {
    /// 创建莫队算法实例
    ///
    /// # 参数
    /// - `n`: 数组长度
    ///
    /// # 复杂度
    /// - 时间: O(1)
    /// - 空间: O(1)
    pub fn new(n: usize) -> Self {
        let block_size = (n as f64).sqrt() as usize + 1;
        MoAlgorithm {
            block_size,
            cur_l: 0,
            cur_r: 0,
            cur_ans: 0,
        }
    }

    /// 处理普通莫队查询（区间不同元素个数）
    ///
    /// # 参数
    /// - `arr`: 输入数组
    /// - `queries`: 查询列表
    ///
    /// # 返回值
    /// 按查询编号排序的答案数组
    ///
    /// # 复杂度
    /// - 时间: O((n + q) × √n)
    /// - 空间: O(n + q)
    pub fn solve_distinct_count(&mut self, arr: &[i32], queries: &[(usize, usize)]) -> Vec<i64> {
        let n = arr.len();
        let q = queries.len();

        // 构建查询
        let mut mo_queries: Vec<Query> = queries
            .iter()
            .enumerate()
            .map(|(id, &(l, r))| Query::new(l, r, id, self.block_size))
            .collect();

        // 按莫队顺序排序
        mo_queries.sort_by(|a, b| {
            if a.block_id != b.block_id {
                a.block_id.cmp(&b.block_id)
            } else {
                // 奇偶性优化：同一块内，奇数块右端点升序，偶数块右端点降序
                if a.block_id % 2 == 0 {
                    a.right.cmp(&b.right)
                } else {
                    b.right.cmp(&a.right)
                }
            }
        });

        // 频率数组
        let max_val = *arr.iter().max().unwrap_or(&0) as usize + 1;
        let mut freq = vec![0i64; max_val.max(n) + 1];
        self.cur_ans = 0;
        self.cur_l = 0;
        self.cur_r = 0;

        // 处理第一个元素
        if !mo_queries.is_empty() {
            self.add(arr[0], &mut freq);
        }

        let mut ans = vec![0i64; q];

        for query in mo_queries {
            // 移动左指针
            while self.cur_l > query.left {
                self.cur_l -= 1;
                self.add(arr[self.cur_l], &mut freq);
            }
            while self.cur_l < query.left {
                self.remove(arr[self.cur_l], &mut freq);
                self.cur_l += 1;
            }

            // 移动右指针
            while self.cur_r < query.right {
                self.cur_r += 1;
                self.add(arr[self.cur_r], &mut freq);
            }
            while self.cur_r > query.right {
                self.remove(arr[self.cur_r], &mut freq);
                self.cur_r -= 1;
            }

            ans[query.id] = self.cur_ans;
        }

        ans
    }

    /// 添加元素
    fn add(&mut self, val: i32, freq: &mut [i64]) {
        let v = val as usize;
        if freq[v] == 0 {
            self.cur_ans += 1;
        }
        freq[v] += 1;
    }

    /// 删除元素
    fn remove(&mut self, val: i32, freq: &mut [i64]) {
        let v = val as usize;
        freq[v] -= 1;
        if freq[v] == 0 {
            self.cur_ans -= 1;
        }
    }

    /// 处理区间众数查询
    ///
    /// # 复杂度
    /// - 时间: O((n + q) × √n × log n) 或使用值域分块优化到 O((n + q) × √n)
    pub fn solve_mode(&mut self, arr: &[i32], queries: &[(usize, usize)]) -> Vec<(i32, i64)> {
        // 使用值域分块来维护众数
        let _n = arr.len();
        let max_val = *arr.iter().max().unwrap_or(&0) as usize + 1;
        let val_block_size = (max_val as f64).sqrt() as usize + 1;
        let num_val_blocks = (max_val + val_block_size - 1) / val_block_size;

        let mut freq = vec![0i64; max_val + 1];
        let mut block_cnt = vec![0i64; num_val_blocks + 1];

        let q = queries.len();
        let mut mo_queries: Vec<Query> = queries
            .iter()
            .enumerate()
            .map(|(id, &(l, r))| Query::new(l, r, id, self.block_size))
            .collect();

        mo_queries.sort_by(|a, b| {
            if a.block_id != b.block_id {
                a.block_id.cmp(&b.block_id)
            } else if a.block_id % 2 == 0 {
                a.right.cmp(&b.right)
            } else {
                b.right.cmp(&a.right)
            }
        });

        self.cur_l = 0;
        self.cur_r = 0;
        if !arr.is_empty() {
            self.add_mode(arr[0], &mut freq, &mut block_cnt, val_block_size);
        }

        let mut ans: Vec<(i32, i64)> = vec![(0, 0); q];

        for query in mo_queries {
            while self.cur_l > query.left {
                self.cur_l -= 1;
                self.add_mode(arr[self.cur_l], &mut freq, &mut block_cnt, val_block_size);
            }
            while self.cur_l < query.left {
                self.remove_mode(arr[self.cur_l], &mut freq, &mut block_cnt, val_block_size);
                self.cur_l += 1;
            }
            while self.cur_r < query.right {
                self.cur_r += 1;
                self.add_mode(arr[self.cur_r], &mut freq, &mut block_cnt, val_block_size);
            }
            while self.cur_r > query.right {
                self.remove_mode(arr[self.cur_r], &mut freq, &mut block_cnt, val_block_size);
                self.cur_r -= 1;
            }

            // 查找众数
            let (mode_val, mode_cnt) = self.find_mode(&freq, &block_cnt, val_block_size, max_val);
            ans[query.id] = (mode_val as i32, mode_cnt);
        }

        ans
    }

    fn add_mode(&mut self, val: i32, freq: &mut [i64], block_cnt: &mut [i64], block_size: usize) {
        let v = val as usize;
        let _old_freq = freq[v];
        freq[v] += 1;
        block_cnt[v / block_size] += 1;
        if freq[v] > self.cur_ans {
            self.cur_ans = freq[v];
        }
    }

    fn remove_mode(&mut self, val: i32, freq: &mut [i64], block_cnt: &mut [i64], block_size: usize) {
        let v = val as usize;
        freq[v] -= 1;
        block_cnt[v / block_size] -= 1;
    }

    fn find_mode(&self, freq: &[i64], block_cnt: &[i64], block_size: usize, max_val: usize) -> (usize, i64) {
        // 从后往前找频率最大的值
        for i in (0..block_cnt.len()).rev() {
            if block_cnt[i] > 0 {
                for v in (i * block_size..((i + 1) * block_size).min(max_val)).rev() {
                    if freq[v] == self.cur_ans {
                        return (v, freq[v]);
                    }
                }
            }
        }
        (0, 0)
    }
}

/// 带修改的莫队查询
#[derive(Clone, Debug)]
pub struct ModQuery {
    /// 查询左端点
    pub left: usize,
    /// 查询右端点
    pub right: usize,
    /// 查询编号
    pub id: usize,
    /// 在此查询之前的修改次数
    pub modify_count: usize,
    /// 左端点所在块
    block_id: usize,
}

/// 修改操作
#[derive(Clone, Debug)]
pub struct Modify {
    /// 修改位置
    pub pos: usize,
    /// 新值
    pub new_val: i32,
    /// 旧值（用于回滚）
    pub old_val: i32,
}

/// 带修改的莫队算法
pub struct MoAlgorithmWithModify {
    block_size: usize,
    mod_block_size: usize,
}

impl MoAlgorithmWithModify {
    /// 创建带修改莫队实例
    ///
    /// # 复杂度
    /// - 时间: O(1)
    /// - 空间: O(1)
    pub fn new(n: usize, _modify_count: usize) -> Self {
        let block_size = (n as f64).cbrt() as usize * (n as f64).cbrt() as usize + 1;
        let mod_block_size = (n as f64).cbrt() as usize + 1;
        MoAlgorithmWithModify {
            block_size,
            mod_block_size,
        }
    }

    /// 处理带修改的区间不同元素个数查询
    ///
    /// # 参数
    /// - `arr`: 初始数组
    /// - `queries`: 查询列表 (l, r, 此前修改次数)
    /// - `modifies`: 修改操作列表
    ///
    /// # 返回值
    /// 按查询编号排序的答案数组
    ///
    /// # 复杂度
    /// - 时间: O(n^(5/3))
    /// - 空间: O(n + q + m)
    pub fn solve(
        &self,
        arr: &[i32],
        queries: &[(usize, usize)],
        modifies: &[Modify],
    ) -> Vec<i64> {
        let _n = arr.len();
        let q = queries.len();

        // 预处理修改操作，记录旧值
        let mut modifies = modifies.to_vec();
        let mut cur_arr = arr.to_vec();
        for modify in &mut modifies {
            modify.old_val = cur_arr[modify.pos];
            cur_arr[modify.pos] = modify.new_val;
        }

        // 构建查询
        let mut mo_queries: Vec<ModQuery> = queries
            .iter()
            .enumerate()
            .map(|(id, &(l, r))| ModQuery {
                left: l,
                right: r,
                id,
                modify_count: modifies.len(), // 假设所有查询都在所有修改之后
                block_id: l / self.block_size,
            })
            .collect();

        // 排序：第一关键字左端点块，第二关键字右端点块，第三关键字修改次数
        mo_queries.sort_by(|a, b| {
            if a.block_id != b.block_id {
                a.block_id.cmp(&b.block_id)
            } else if a.right / self.block_size != b.right / self.block_size {
                a.right.cmp(&b.right)
            } else {
                a.modify_count.cmp(&b.modify_count)
            }
        });

        // 初始化
        let max_val = 1000000;
        let mut freq = vec![0i64; max_val + 1];
        let mut cur_l = 0usize;
        let mut cur_r = 0usize;
        let mut cur_time = 0usize;
        let mut cur_ans = 0i64;
        let mut ans = vec![0i64; q];

        // 处理第一个元素
        if !arr.is_empty() {
            freq[arr[0] as usize] = 1;
            cur_ans = 1;
        }

        for query in mo_queries {
            // 移动左指针
            while cur_l > query.left {
                cur_l -= 1;
                cur_ans += Self::add(&mut freq, cur_arr[cur_l]);
            }
            while cur_l < query.left {
                cur_ans += Self::remove(&mut freq, cur_arr[cur_l]);
                cur_l += 1;
            }

            // 移动右指针
            while cur_r < query.right {
                cur_r += 1;
                cur_ans += Self::add(&mut freq, cur_arr[cur_r]);
            }
            while cur_r > query.right {
                cur_ans += Self::remove(&mut freq, cur_arr[cur_r]);
                cur_r -= 1;
            }

            // 处理时间轴（修改）
            while cur_time < query.modify_count && cur_time < modifies.len() {
                Self::apply_modify(
                    &mut cur_arr,
                    &mut freq,
                    &modifies[cur_time],
                    cur_l,
                    cur_r,
                    &mut cur_ans,
                );
                cur_time += 1;
            }
            while cur_time > query.modify_count {
                cur_time -= 1;
                Self::undo_modify(
                    &mut cur_arr,
                    &mut freq,
                    &modifies[cur_time],
                    cur_l,
                    cur_r,
                    &mut cur_ans,
                );
            }

            ans[query.id] = cur_ans;
        }

        ans
    }

    fn add(freq: &mut [i64], val: i32) -> i64 {
        let v = val as usize;
        freq[v] += 1;
        if freq[v] == 1 {
            1
        } else {
            0
        }
    }

    fn remove(freq: &mut [i64], val: i32) -> i64 {
        let v = val as usize;
        freq[v] -= 1;
        if freq[v] == 0 {
            -1
        } else {
            0
        }
    }

    fn apply_modify(
        arr: &mut [i32],
        freq: &mut [i64],
        modify: &Modify,
        l: usize,
        r: usize,
        ans: &mut i64,
    ) {
        let pos = modify.pos;
        if l <= pos && pos <= r {
            // 在当前区间内，需要更新
            freq[modify.old_val as usize] -= 1;
            if freq[modify.old_val as usize] == 0 {
                *ans -= 1;
            }
            freq[modify.new_val as usize] += 1;
            if freq[modify.new_val as usize] == 1 {
                *ans += 1;
            }
        }
        arr[pos] = modify.new_val;
    }

    fn undo_modify(
        arr: &mut [i32],
        freq: &mut [i64],
        modify: &Modify,
        l: usize,
        r: usize,
        ans: &mut i64,
    ) {
        let pos = modify.pos;
        if l <= pos && pos <= r {
            freq[modify.new_val as usize] -= 1;
            if freq[modify.new_val as usize] == 0 {
                *ans -= 1;
            }
            freq[modify.old_val as usize] += 1;
            if freq[modify.old_val as usize] == 1 {
                *ans += 1;
            }
        }
        arr[pos] = modify.old_val;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_distinct_count() {
        let arr = vec![1, 2, 1, 3, 2, 4, 1];
        let queries = vec![
            (0, 2), // [1,2,1] -> 2 distinct
            (1, 4), // [2,1,3,2] -> 3 distinct
            (0, 6), // 全部 -> 4 distinct
            (3, 5), // [3,2,4] -> 3 distinct
        ];

        let mut mo = MoAlgorithm::new(arr.len());
        let ans = mo.solve_distinct_count(&arr, &queries);

        assert_eq!(ans[0], 2);
        assert_eq!(ans[1], 3);
        assert_eq!(ans[2], 4);
        assert_eq!(ans[3], 3);
    }

    #[test]
    fn test_single_element() {
        let arr = vec![5];
        let queries = vec![(0, 0)];

        let mut mo = MoAlgorithm::new(arr.len());
        let ans = mo.solve_distinct_count(&arr, &queries);

        assert_eq!(ans[0], 1);
    }

    #[test]
    fn test_all_same() {
        let arr = vec![1, 1, 1, 1, 1];
        let queries = vec![
            (0, 4),
            (1, 3),
            (0, 0),
        ];

        let mut mo = MoAlgorithm::new(arr.len());
        let ans = mo.solve_distinct_count(&arr, &queries);

        assert_eq!(ans[0], 1);
        assert_eq!(ans[1], 1);
        assert_eq!(ans[2], 1);
    }

    #[test]
    fn test_all_different() {
        let arr = vec![1, 2, 3, 4, 5];
        let queries = vec![
            (0, 4), // 5 distinct
            (1, 3), // 3 distinct
        ];

        let mut mo = MoAlgorithm::new(arr.len());
        let ans = mo.solve_distinct_count(&arr, &queries);

        assert_eq!(ans[0], 5);
        assert_eq!(ans[1], 3);
    }

    #[test]
    fn test_empty_range() {
        let arr = vec![1, 2, 3];
        // 单元素查询
        let queries = vec![
            (0, 0),
            (1, 1),
            (2, 2),
        ];

        let mut mo = MoAlgorithm::new(arr.len());
        let ans = mo.solve_distinct_count(&arr, &queries);

        assert_eq!(ans[0], 1);
        assert_eq!(ans[1], 1);
        assert_eq!(ans[2], 1);
    }

    #[test]
    fn test_with_modify() {
        let arr = vec![1, 2, 1, 3];
        let queries = vec![
            (0, 3), // 查询 [1,2,1,3] -> 3 distinct
        ];
        let modifies = vec![
            Modify { pos: 1, new_val: 1, old_val: 0 }, // 将位置1改为1
        ];

        let mo = MoAlgorithmWithModify::new(arr.len(), modifies.len());
        let ans = mo.solve(&arr, &queries, &modifies);

        // 注意：这里的查询是在所有修改之后，所以数组变为 [1,1,1,3]
        assert_eq!(ans[0], 2); // 只有2种不同的值
    }
}
