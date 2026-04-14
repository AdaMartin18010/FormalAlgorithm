//! 舞蹈链（Dancing Links / DLX）
//!
//! 舞蹈链是Donald Knuth提出的精确覆盖问题的高效求解算法。
//! 使用双向循环链表实现，删除和恢复操作都是 O(1)。
//!
//! # 精确覆盖问题
//! 给定一个由0和1组成的矩阵，选择一些行使得每一列恰好有一个1。
//!
//! # 算法原理
//! 1. 使用双向循环十字链表表示稀疏矩阵
//! 2. 选择1最少的列进行分支
//! 3. 递归尝试选择覆盖该列的每一行
//! 4. 删除与选中行冲突的所有行和列
//! 5. 回溯时恢复（舞蹈）
//!
//! # 时间复杂度
//! - 最坏情况: O(分支因子^深度)
//! - 实际表现: 对精确覆盖问题非常高效
//! - 空间: O(矩阵中1的数量)
//!
//! # 应用场景
//! - 数独求解
//! - N皇后问题
//! - 拼图问题（如Pentomino）
//! - 拉丁方
//! - 图着色

/// 舞蹈链节点
#[derive(Clone, Debug)]
struct Node {
    /// 左指针（索引）
    left: usize,
    /// 右指针（索引）
    right: usize,
    /// 上指针（索引）
    up: usize,
    /// 下指针（索引）
    down: usize,
    /// 列头索引
    col: usize,
    /// 行号
    row: usize,
}

impl Node {
    fn new(row: usize, col: usize) -> Self {
        Node {
            left: 0,
            right: 0,
            up: 0,
            down: 0,
            col,
            row,
        }
    }
}

/// 列头节点
#[derive(Clone, Debug)]
struct Column {
    /// 节点索引（作为链表头）
    head: usize,
    /// 列大小（该列中1的数量）
    size: usize,
    /// 列名（用于输出）
    name: String,
    /// 左指针
    left: usize,
    /// 右指针
    right: usize,
}

impl Column {
    fn new(index: usize, name: String) -> Self {
        Column {
            head: index,
            size: 0,
            name,
            left: 0,
            right: 0,
        }
    }
}

/// 舞蹈链求解器
pub struct DancingLinks {
    /// 所有节点（包括列头和普通节点）
    nodes: Vec<Node>,
    /// 列头数组
    columns: Vec<Column>,
    /// 根节点索引（列头列表的头）
    root: usize,
    /// 当前解决方案（选中的行）
    solution: Vec<usize>,
    /// 所有解决方案
    all_solutions: Vec<Vec<usize>>,
    /// 最大解数量（防止无限搜索）
    max_solutions: usize,
    /// 当前解数量
    solution_count: usize,
    /// 原始行数据（用于输出）
    row_names: Vec<String>,
}

/// 求解结果
#[derive(Debug, Clone)]
pub struct DLXResult {
    /// 是否找到解
    pub has_solution: bool,
    /// 所有解决方案（每行是一个解，解是原始行索引的列表）
    pub solutions: Vec<Vec<usize>>,
    /// 解的数量
    pub count: usize,
}

impl DancingLinks {
    /// 从矩阵创建舞蹈链
    ///
    /// # 参数
    /// - `matrix`: 0-1矩阵，每行是一个Vec<bool>
    /// - `col_names`: 列名（可选）
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::DancingLinks;
    /// let matrix = vec![
    ///     vec![true, false, true, false],
    ///     vec![true, true, false, false],
    ///     vec![false, true, true, true],
    /// ];
    /// let dlx = DancingLinks::new(&matrix, None);
    /// ```
    pub fn new(matrix: &[Vec<bool>], col_names: Option<Vec<String>>) -> Self {
        if matrix.is_empty() {
            return DancingLinks {
                nodes: Vec::new(),
                columns: Vec::new(),
                root: 0,
                solution: Vec::new(),
                all_solutions: Vec::new(),
                max_solutions: 1,
                solution_count: 0,
                row_names: Vec::new(),
            };
        }

        let num_rows = matrix.len();
        let num_cols = matrix[0].len();

        // 创建列名
        let names: Vec<String> = match col_names {
            Some(names) => names,
            None => (0..num_cols).map(|i| format!("C{}", i)).collect(),
        };

        // 初始化列头
        let mut columns: Vec<Column> = Vec::with_capacity(num_cols);
        let mut nodes: Vec<Node> = Vec::new();

        // 根节点（索引0）
        nodes.push(Node::new(0, 0));

        // 创建列头节点
        for i in 0..num_cols {
            let col_idx = nodes.len();
            columns.push(Column::new(col_idx, names[i].clone()));
            nodes.push(Node::new(0, col_idx));

            // 列头的上下指针指向自己
            let idx = nodes.len() - 1;
            nodes[idx].up = idx;
            nodes[idx].down = idx;
        }

        // 连接列头形成循环链表
        for i in 0..num_cols {
            let curr = columns[i].head;
            let left = if i == 0 {
                columns[num_cols - 1].head
            } else {
                columns[i - 1].head
            };
            let right = if i == num_cols - 1 {
                columns[0].head
            } else {
                columns[i + 1].head
            };

            nodes[curr].left = left;
            nodes[curr].right = right;
            columns[i].left = left;
            columns[i].right = right;
        }

        // 根节点连接
        nodes[0].right = columns[0].head;
        nodes[0].left = columns[num_cols - 1].head;
        nodes[columns[0].head].left = 0;
        nodes[columns[num_cols - 1].head].right = 0;

        // 添加矩阵行
        let mut row_names: Vec<String> = Vec::with_capacity(num_rows);
        for (row_idx, row) in matrix.iter().enumerate() {
            row_names.push(format!("R{}", row_idx));

            let mut row_nodes: Vec<usize> = Vec::new();

            // 为这一行中的每个1创建节点
            for (col_idx, &val) in row.iter().enumerate() {
                if val {
                    let node_idx = nodes.len();
                    nodes.push(Node::new(row_idx, columns[col_idx].head));
                    row_nodes.push(node_idx);

                    // 更新列大小
                    columns[col_idx].size += 1;

                    // 插入到列的链表中
                    let col_head = columns[col_idx].head;
                    let last_in_col = nodes[col_head].up;

                    nodes[node_idx].up = last_in_col;
                    nodes[node_idx].down = col_head;
                    nodes[last_in_col].down = node_idx;
                    nodes[col_head].up = node_idx;
                }
            }

            // 连接同一行的节点（左右指针）
            for i in 0..row_nodes.len() {
                let curr = row_nodes[i];
                let left = if i == 0 {
                    row_nodes[row_nodes.len() - 1]
                } else {
                    row_nodes[i - 1]
                };
                let right = if i == row_nodes.len() - 1 {
                    row_nodes[0]
                } else {
                    row_nodes[i + 1]
                };

                nodes[curr].left = left;
                nodes[curr].right = right;
            }
        }

        DancingLinks {
            nodes,
            columns,
            root: 0,
            solution: Vec::new(),
            all_solutions: Vec::new(),
            max_solutions: 1,
            solution_count: 0,
            row_names,
        }
    }

    /// 设置最大解数量
    pub fn with_max_solutions(mut self, max: usize) -> Self {
        self.max_solutions = max;
        self
    }

    /// 覆盖一列
    fn cover(&mut self, col: usize) {
        // 从列头列表中移除
        let left = self.nodes[col].left;
        let right = self.nodes[col].right;
        self.nodes[left].right = right;
        self.nodes[right].left = left;

        // 遍历该列的每个节点
        let mut row = self.nodes[col].down;
        while row != col {
            // 移除这一行的所有其他节点
            let mut col_node = self.nodes[row].right;
            while col_node != row {
                let up = self.nodes[col_node].up;
                let down = self.nodes[col_node].down;
                self.nodes[up].down = down;
                self.nodes[down].up = up;

                let col_idx = self.nodes[col_node].col;
                self.columns[col_idx - 1].size -= 1;

                col_node = self.nodes[col_node].right;
            }
            row = self.nodes[row].down;
        }
    }

    /// 恢复一列（逆向操作）
    fn uncover(&mut self, col: usize) {
        // 逆序恢复
        let mut row = self.nodes[col].up;
        while row != col {
            let mut col_node = self.nodes[row].left;
            while col_node != row {
                let col_idx = self.nodes[col_node].col;
                self.columns[col_idx - 1].size += 1;

                let up = self.nodes[col_node].up;
                let down = self.nodes[col_node].down;
                self.nodes[up].down = col_node;
                self.nodes[down].up = col_node;

                col_node = self.nodes[col_node].left;
            }
            row = self.nodes[row].up;
        }

        // 恢复到列头列表
        let left = self.nodes[col].left;
        let right = self.nodes[col].right;
        self.nodes[left].right = col;
        self.nodes[right].left = col;
    }

    /// 求解精确覆盖问题
    ///
    /// # 返回值
    /// 返回 `DLXResult`，包含所有找到的解
    ///
    /// # 示例
    /// ```
/// use formal_algorithms::DancingLinks;
    /// let matrix = vec![
    ///     vec![true, false, true],
    ///     vec![true, true, false],
    ///     vec![false, true, true],
    /// ];
    /// let mut dlx = DancingLinks::new(&matrix, None);
    /// let result = dlx.solve();
    /// ```
    pub fn solve(&mut self) -> DLXResult {
        self.solution.clear();
        self.all_solutions.clear();
        self.solution_count = 0;

        self.search();

        DLXResult {
            has_solution: !self.all_solutions.is_empty(),
            solutions: self.all_solutions.clone(),
            count: self.all_solutions.len(),
        }
    }

    /// 递归搜索
    fn search(&mut self) {
        if self.solution_count >= self.max_solutions {
            return;
        }

        // 处理空矩阵情况
        if self.columns.is_empty() {
            self.all_solutions.push(self.solution.clone());
            self.solution_count += 1;
            return;
        }

        // 检查是否完成
        if self.nodes[self.root].right == self.root {
            // 所有列都被覆盖，找到一个解
            self.all_solutions.push(self.solution.clone());
            self.solution_count += 1;
            return;
        }

        // 选择1最少的列（启发式）
        let mut min_col = self.nodes[self.root].right;
        let mut min_size = self.columns[min_col - 1].size;

        let mut col = self.nodes[self.root].right;
        while col != self.root {
            let size = self.columns[col - 1].size;
            if size < min_size {
                min_size = size;
                min_col = col;
                if size == 0 {
                    // 无解
                    return;
                }
            }
            col = self.nodes[col].right;
        }

        if min_size == 0 {
            return;
        }

        // 覆盖选中的列
        self.cover(min_col);

        // 尝试每一行
        let mut row = self.nodes[min_col].down;
        while row != min_col {
            // 选择这一行
            self.solution.push(self.nodes[row].row);

            // 覆盖这一行中所有1所在的列
            let mut col_node = self.nodes[row].right;
            while col_node != row {
                self.cover(self.nodes[col_node].col);
                col_node = self.nodes[col_node].right;
            }

            // 递归搜索
            self.search();

            // 回溯：恢复这一行中所有1所在的列
            col_node = self.nodes[row].left;
            while col_node != row {
                self.uncover(self.nodes[col_node].col);
                col_node = self.nodes[col_node].left;
            }

            // 移除这一行
            self.solution.pop();

            row = self.nodes[row].down;
        }

        // 恢复选中的列
        self.uncover(min_col);
    }

    /// 获取解的详细描述
    pub fn describe_solution(&self, sol: &[usize]) -> String {
        let rows: Vec<String> = sol.iter()
            .map(|&r| self.row_names[r].clone())
            .collect();
        format!("Solution: [{}]", rows.join(", "))
    }
}

impl DLXResult {
    /// 打印结果
    pub fn print(&self) {
        if self.has_solution {
            println!("找到 {} 个解:", self.count);
            for (i, sol) in self.solutions.iter().enumerate() {
                println!("  解 {}: {:?}", i + 1, sol);
            }
        } else {
            println!("无解");
        }
    }
}

/// 辅助函数：快速求解精确覆盖问题
pub fn exact_cover(matrix: &[Vec<bool>]) -> DLXResult {
    let mut dlx = DancingLinks::new(matrix, None);
    dlx.solve()
}

/// 辅助函数：求解并获取所有解
pub fn exact_cover_all(matrix: &[Vec<bool>]) -> DLXResult {
    let mut dlx = DancingLinks::new(matrix, None).with_max_solutions(1000);
    dlx.solve()
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_simple_cover() {
        // 简单测试：3列，选择一行覆盖所有列
        let matrix = vec![
            vec![true, true, true],
        ];

        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        assert!(result.has_solution);
        assert_eq!(result.count, 1);
        assert_eq!(result.solutions[0], vec![0]);
    }

    #[test]
    fn test_multiple_solutions() {
        // 多个解的情况
        // 需要选择行使得每列恰好有一个1
        let matrix = vec![
            vec![true, false],
            vec![false, true],
            vec![true, true],
        ];

        let mut dlx = DancingLinks::new(&matrix, None).with_max_solutions(10);
        let result = dlx.solve();

        // 解: [0,1] 或 [2]
        assert!(result.count >= 1);
    }

    #[test]
    fn test_no_solution() {
        // 无解的情况
        let matrix = vec![
            vec![true, false],
            vec![true, false],
        ];

        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        assert!(!result.has_solution);
        assert_eq!(result.count, 0);
    }

    #[test]
    fn test_pentomino_subset() {
        // Pentomino问题的一个简化版本
        // 6列，需要精确覆盖
        let matrix = vec![
            vec![true, false, false, true, false, false],  // 行0
            vec![true, false, false, false, true, false],  // 行1
            vec![false, true, false, true, false, false],  // 行2
            vec![false, true, false, false, true, true],   // 行3
            vec![false, false, true, false, false, true],  // 行4
        ];

        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        // 这个矩阵应该有解
        println!("Pentomino-like solutions: {}", result.count);
    }

    #[test]
    fn test_empty_matrix() {
        let matrix: Vec<Vec<bool>> = vec![];
        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        // 空矩阵应该有一个解（空解）
        assert!(result.has_solution);
    }

    #[test]
    fn test_single_column() {
        let matrix = vec![
            vec![true],
            vec![true],
            vec![true],
        ];

        let mut dlx = DancingLinks::new(&matrix, None).with_max_solutions(10);
        let result = dlx.solve();

        assert_eq!(result.count, 3); // 3个解，每行一个
    }

    #[test]
    fn test_convenience_function() {
        let matrix = vec![
            vec![true, false, true],
            vec![true, true, false],
            vec![false, true, true],
        ];

        let result = exact_cover(&matrix);
        assert!(result.count > 0);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    /// 将数独转换为精确覆盖问题
    fn sudoku_to_exact_cover() -> Vec<Vec<bool>> {
        // 数独有729行（9x9x9，每个格子9种可能）和324列
        // 324 = 81（格子约束）+ 81（行约束）+ 81（列约束）+ 81（宫约束）
        // 这里简化演示，生成部分约束

        let matrix = Vec::new();

        // 为简化，只生成一个小的子集
        // 实际的数独转换需要完整的729x324矩阵

        // 示例：某个位置填某个数
        // 行：表示(行, 列, 数)的组合
        // 列：表示约束

        matrix
    }

    #[test]
    fn n_queens_as_exact_cover() {
        println!("\n=== N皇后作为精确覆盖问题 ===");

        // 4皇后问题
        // 需要满足：每行一个皇后，每列一个皇后，每个对角线最多一个皇后
        // 简化为精确覆盖：4行4列，共8个约束

        // 每行表示一个皇后的位置
        // 列0-3: 行约束
        // 列4-7: 列约束

        let mut matrix: Vec<Vec<bool>> = Vec::new();

        for row in 0..4 {
            for col in 0..4 {
                let mut r = vec![false; 8];
                r[row] = true;      // 行约束
                r[4 + col] = true;  // 列约束
                matrix.push(r);
            }
        }

        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        println!("4皇后解的数量: {}", result.count);
        if result.has_solution {
            println!("一个解: {:?}", result.solutions[0]);
            // 将解转换为棋盘位置
            println!("皇后位置:");
            for &row_idx in &result.solutions[0] {
                let row = row_idx / 4;
                let col = row_idx % 4;
                println!("  ({}, {})", row, col);
            }
        }
    }

    #[test]
    fn tiling_problem() {
        println!("\n=== 铺砖问题 ===");

        // 2x3矩形用1x2多米诺骨牌铺满
        // 6个格子，每个格子需要被覆盖
        // 每块骨牌覆盖2个相邻格子

        // 列：6个格子的覆盖约束
        // 行：所有可能的骨牌放置方式

        let mut matrix: Vec<Vec<bool>> = Vec::new();

        // 格子编号：
        // 0 1 2
        // 3 4 5

        // 水平放置
        matrix.push(vec![true, true, false, false, false, false]);  // (0,1)
        matrix.push(vec![false, true, true, false, false, false]);  // (1,2)
        matrix.push(vec![false, false, false, true, true, false]);  // (3,4)
        matrix.push(vec![false, false, false, false, true, true]);  // (4,5)

        // 垂直放置
        matrix.push(vec![true, false, false, true, false, false]);  // (0,3)
        matrix.push(vec![false, true, false, false, true, false]);  // (1,4)
        matrix.push(vec![false, false, true, false, false, true]);  // (2,5)

        let mut dlx = DancingLinks::new(&matrix, None);
        let result = dlx.solve();

        println!("2x3矩形用1x2骨牌铺满的方法数: {}", result.count);
        for (i, sol) in result.solutions.iter().enumerate() {
            println!("  方案 {}: {:?}", i + 1, sol);
        }
    }

    #[test]
    fn latin_square_partial() {
        println!("\n=== 拉丁方（部分）===");

        // 2x2拉丁方
        // 每行每列恰好出现1和2各一次

        // 变量：(行, 列, 值)
        // 2x2x2 = 8个变量
        // 约束：
        // - 每个格子恰好一个值（4个约束）
        // - 每行每个值恰好一次（4个约束）
        // - 每列每个值恰好一次（4个约束）

        // 简化为12列的精确覆盖问题

        let _matrix = vec![
            // (0,0,1): 格子(0,0), 行0值1, 列0值1
            vec![true, false, false, false, true, false, true, false, false, false, false, false],
            // (0,0,2): 格子(0,0), 行0值2, 列0值2
            vec![true, false, false, false, false, true, false, true, false, false, false, false],
            // ... 其他组合
        ];

        // 完整实现需要所有8个变量的约束
        println!("2x2拉丁方的变量约束示例");
        println!("变量 (行,列,值) 需要满足格子、行值、列值三个约束");
    }

    #[test]
    fn exact_cover_visualization() {
        println!("\n=== 精确覆盖可视化 ===");

        // 一个直观的例子
        let matrix = vec![
            //   A B C D E
            vec![true, false, true, false, false],   // 1
            vec![true, true, false, false, false],   // 2
            vec![false, true, false, true, false],   // 3
            vec![false, false, true, false, true],   // 4
            vec![false, true, false, false, true],   // 5
        ];

        let col_names: Vec<String> = vec!["A", "B", "C", "D", "E"]
            .iter()
            .map(|&s| s.to_string())
            .collect();

        let mut dlx = DancingLinks::new(&matrix, Some(col_names));
        let result = dlx.solve();

        println!("矩阵:");
        println!("    A B C D E");
        for (i, row) in matrix.iter().enumerate() {
            print!("{}: ", i + 1);
            for &val in row {
                print!("{} ", if val { "1" } else { "0" });
            }
            println!();
        }

        println!("\n解:");
        for (i, sol) in result.solutions.iter().enumerate() {
            print!("  方案 {}: 行 ", i + 1);
            for &row in sol {
                print!("{}, ", row + 1);
            }
            println!();

            // 验证覆盖
            let mut covered = vec![false; 5];
            for &row in sol {
                for (c, &val) in matrix[row].iter().enumerate() {
                    if val {
                        covered[c] = true;
                    }
                }
            }
            println!("    覆盖列: {:?}", covered);
        }
    }
}
