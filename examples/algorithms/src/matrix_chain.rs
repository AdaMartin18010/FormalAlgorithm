//! 矩阵链乘法（动态规划）
//!
//! 矩阵链乘法问题研究如何以最优顺序计算一系列矩阵的乘积，使得标量乘法次数最少。
//! 由于矩阵乘法满足结合律，不同的计算顺序会导致不同的计算代价。
//!
//! # 问题定义
//! 给定矩阵链 A₁ × A₂ × ... × Aₙ，其中矩阵 Aᵢ 的维度为 p[i-1] × p[i]，
//! 找到最优的括号化方案，使得计算乘积所需的标量乘法次数最少。
//!
//! # 动态规划解法
//! - 状态定义：m[i][j] 表示计算 Aᵢ × ... × Aⱼ 的最小代价
//! - 状态转移：m[i][j] = min(m[i][k] + m[k+1][j] + p[i-1]·p[k]·p[j])
//! - 时间复杂度：O(n³)
//! - 空间复杂度：O(n²)
//!
//! # 示例
//! 矩阵维度：[10, 30, 5, 60]
//! 表示：A₁(10×30), A₂(30×5), A₃(5×60)
//! 最优括号化：(A₁ × A₂) × A₃，代价 = 10×30×5 + 10×5×60 = 4500
//!
//! # 应用
//! - 科学计算优化
//! - 编译器优化
//! - 图形学中的变换组合

use std::fmt::{Display, Formatter, Result as FmtResult};

/// 矩阵链乘法求解器
#[derive(Debug)]
pub struct MatrixChain {
    /// 维度数组，矩阵i的维度为 dims[i] × dims[i+1]
    dims: Vec<usize>,
    /// 最小代价表
    m: Vec<Vec<usize>>,
    /// 分割点表（用于重构最优解）
    s: Vec<Vec<usize>>,
    /// 矩阵数量
    n: usize,
}

/// 最优解信息
#[derive(Debug, Clone)]
pub struct OptimalSolution {
    /// 最小乘法次数
    pub min_cost: usize,
    /// 最优括号化方案
    pub parenthesization: String,
    /// 计算步骤
    pub steps: Vec<String>,
}

impl Display for OptimalSolution {
    fn fmt(&self, f: &mut Formatter<'_>) -> FmtResult {
        writeln!(f, "Minimum cost: {}", self.min_cost)?;
        writeln!(f, "Optimal parenthesization: {}", self.parenthesization)?;
        writeln!(f, "Computation steps:")?;
        for (i, step) in self.steps.iter().enumerate() {
            writeln!(f, "  {}. {}", i + 1, step)?;
        }
        Ok(())
    }
}

impl MatrixChain {
    /// 创建矩阵链求解器
    ///
    /// # 参数
    /// - `dims`: 维度数组，包含n+1个元素，表示n个矩阵的维度
    ///   矩阵i的维度为 dims[i-1] × dims[i]
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::matrix_chain::MatrixChain;
    /// // 3个矩阵：A₁(10×30), A₂(30×5), A₃(5×60)
    /// let mc = MatrixChain::new(vec![10, 30, 5, 60]);
    /// ```
    pub fn new(dims: Vec<usize>) -> Self {
        let n = dims.len().saturating_sub(1);
        MatrixChain {
            dims,
            m: vec![vec![0; n + 1]; n + 1],
            s: vec![vec![0; n + 1]; n + 1],
            n,
        }
    }

    /// 求解最优矩阵链乘法顺序
    ///
    /// 使用动态规划填充代价表和分割点表
    pub fn solve(&mut self) -> usize {
        if self.n <= 1 {
            return 0;
        }

        // l 表示链的长度
        for l in 2..=self.n {
            // i 表示起始矩阵
            for i in 1..=self.n - l + 1 {
                let j = i + l - 1; // 结束矩阵
                self.m[i][j] = usize::MAX;

                // 尝试所有可能的分割点
                for k in i..j {
                    let cost = self.m[i][k] + self.m[k + 1][j]
                        + self.dims[i - 1] * self.dims[k] * self.dims[j];

                    if cost < self.m[i][j] {
                        self.m[i][j] = cost;
                        self.s[i][j] = k;
                    }
                }
            }
        }

        self.m[1][self.n]
    }

    /// 获取最优解的完整信息
    pub fn get_solution(&self) -> OptimalSolution {
        let min_cost = if self.n == 0 { 0 } else { self.m[1][self.n] };
        let parenthesization = self.print_optimal_parens(1, self.n);
        let steps = self.get_computation_steps();

        OptimalSolution {
            min_cost,
            parenthesization,
            steps,
        }
    }

    /// 打印最优括号化方案
    fn print_optimal_parens(&self, i: usize, j: usize) -> String {
        if i == j {
            format!("A{}", i)
        } else {
            let k = self.s[i][j];
            format!(
                "({})",
                self.print_optimal_parens(i, k) + " × " + &self.print_optimal_parens(k + 1, j)
            )
        }
    }

    /// 获取计算步骤
    fn get_computation_steps(&self) -> Vec<String> {
        let mut steps = Vec::new();
        self.build_steps(1, self.n, &mut steps);
        steps
    }

    fn build_steps(&self, i: usize, j: usize, steps: &mut Vec<String>) -> String {
        if i == j {
            format!("A{}[{}×{}]", i, self.dims[i - 1], self.dims[i])
        } else {
            let k = self.s[i][j];
            let left = self.build_steps(i, k, steps);
            let right = self.build_steps(k + 1, j, steps);
            let result = format!("M{}{}", i, j);
            let cost = self.dims[i - 1] * self.dims[k] * self.dims[j];
            steps.push(format!(
                "{} = {} × {} (cost: {} = {}×{}×{})",
                result, left, right, cost, self.dims[i - 1], self.dims[k], self.dims[j]
            ));
            result
        }
    }

    /// 获取特定子问题的最小代价
    pub fn get_cost(&self, i: usize, j: usize) -> Option<usize> {
        if i > 0 && j > 0 && i <= self.n && j <= self.n && i <= j {
            Some(self.m[i][j])
        } else {
            None
        }
    }

    /// 打印动态规划表（用于调试）
    pub fn print_dp_table(&self) -> String {
        let mut result = String::new();
        result.push_str("Cost Table (m):\n");
        for i in 1..=self.n {
            for j in 1..=self.n {
                if i > j {
                    result.push_str("    - ");
                } else {
                    result.push_str(&format!("{:5} ", self.m[i][j]));
                }
            }
            result.push('\n');
        }

        result.push_str("\nSplit Table (s):\n");
        for i in 1..=self.n {
            for j in 1..=self.n {
                if i >= j {
                    result.push_str("    - ");
                } else {
                    result.push_str(&format!("{:5} ", self.s[i][j]));
                }
            }
            result.push('\n');
        }

        result
    }

    /// 获取矩阵数量
    pub fn matrix_count(&self) -> usize {
        self.n
    }

    /// 获取维度数组
    pub fn dimensions(&self) -> &[usize] {
        &self.dims
    }
}

/// 贪心算法版本（非最优，用于对比）
pub fn greedy_multiply(dims: &[usize]) -> usize {
    let n = dims.len() - 1;
    if n <= 1 {
        return 0;
    }

    // 贪心策略：总是选择当前代价最小的乘法
    // 这是一个启发式，不一定得到最优解
    let mut cost = 0;
    let mut current_dims: Vec<usize> = dims.to_vec();

    while current_dims.len() > 2 {
        let mut min_cost = usize::MAX;
        let mut min_idx = 0;

        for i in 0..current_dims.len() - 2 {
            let c = current_dims[i] * current_dims[i + 1] * current_dims[i + 2];
            if c < min_cost {
                min_cost = c;
                min_idx = i;
            }
        }

        cost += min_cost;
        // 合并两个矩阵
        current_dims.remove(min_idx + 1);
    }

    cost
}

/// 暴力解法（用于验证小例子）
pub fn brute_force(dims: &[usize]) -> usize {
    let n = dims.len() - 1;
    if n <= 1 {
        return 0;
    }

    fn helper(dims: &[usize], i: usize, j: usize) -> usize {
        if i == j {
            return 0;
        }

        let mut min_cost = usize::MAX;
        for k in i..j {
            let cost = helper(dims, i, k) + helper(dims, k + 1, j)
                + dims[i - 1] * dims[k] * dims[j];
            min_cost = min_cost.min(cost);
        }
        min_cost
    }

    helper(dims, 1, n)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_basic() {
        // 3个矩阵: A1(10×30), A2(30×5), A3(5×60)
        // 最优: (A1×A2)×A3 = 10×30×5 + 10×5×60 = 1500 + 3000 = 4500
        let mut mc = MatrixChain::new(vec![10, 30, 5, 60]);
        let cost = mc.solve();
        assert_eq!(cost, 4500);
    }

    #[test]
    fn test_classic_example() {
        // 经典教材例子
        // A1: 30×35, A2: 35×15, A3: 15×5, A4: 5×10, A5: 10×20, A6: 20×25
        // 最优代价: 15125
        let mut mc = MatrixChain::new(vec![30, 35, 15, 5, 10, 20, 25]);
        let cost = mc.solve();
        assert_eq!(cost, 15125);
    }

    #[test]
    fn test_two_matrices() {
        // 只有两个矩阵，只有一种乘法方式
        let mut mc = MatrixChain::new(vec![10, 20, 30]);
        let cost = mc.solve();
        assert_eq!(cost, 10 * 20 * 30);
    }

    #[test]
    fn test_single_matrix() {
        // 只有一个矩阵，无需乘法
        let mut mc = MatrixChain::new(vec![10, 20]);
        let cost = mc.solve();
        assert_eq!(cost, 0);
    }

    #[test]
    fn test_empty() {
        let mut mc = MatrixChain::new(vec![]);
        let cost = mc.solve();
        assert_eq!(cost, 0);
    }

    #[test]
    fn test_optimal_parens() {
        let mut mc = MatrixChain::new(vec![10, 30, 5, 60]);
        mc.solve();
        let solution = mc.get_solution();
        
        assert!(solution.parenthesization.contains("A1"));
        assert!(solution.parenthesization.contains("A2"));
        assert!(solution.parenthesization.contains("A3"));
        assert_eq!(solution.min_cost, 4500);
    }

    #[test]
    fn test_computation_steps() {
        let mut mc = MatrixChain::new(vec![10, 30, 5, 60]);
        mc.solve();
        let solution = mc.get_solution();
        
        assert!(!solution.steps.is_empty());
        // 3个矩阵需要2次乘法
        assert_eq!(solution.steps.len(), 2);
    }

    #[test]
    fn test_vs_brute_force() {
        // 对小例子比较动态规划和暴力解法
        let dims = vec![10, 20, 30, 40, 50];
        
        let mut mc = MatrixChain::new(dims.clone());
        let dp_cost = mc.solve();
        let bf_cost = brute_force(&dims);
        
        assert_eq!(dp_cost, bf_cost);
    }

    #[test]
    fn test_greedy_vs_optimal() {
        // 贪心算法不一定最优
        let dims = vec![10, 30, 5, 60];
        
        let mut mc = MatrixChain::new(dims.clone());
        let optimal = mc.solve();
        let greedy = greedy_multiply(&dims);
        
        // 最优解 <= 贪心解
        assert!(optimal <= greedy);
    }

    #[test]
    fn test_get_cost() {
        let mut mc = MatrixChain::new(vec![10, 30, 5, 60]);
        mc.solve();
        
        // 单矩阵代价为0
        assert_eq!(mc.get_cost(1, 1), Some(0));
        assert_eq!(mc.get_cost(2, 2), Some(0));
        
        // 两个矩阵
        assert_eq!(mc.get_cost(1, 2), Some(10 * 30 * 5));
        
        // 越界
        assert_eq!(mc.get_cost(0, 1), None);
        assert_eq!(mc.get_cost(1, 10), None);
    }

    #[test]
    fn test_large_chain() {
        // 测试较长的矩阵链
        let dims: Vec<usize> = (1..=20).map(|i| i * 10).collect();
        let mut mc = MatrixChain::new(dims);
        let cost = mc.solve();
        
        assert!(cost > 0);
        assert!(mc.get_solution().parenthesization.len() > 0);
    }
}

/// 使用示例
#[cfg(test)]
mod example {
    use super::*;

    #[test]
    fn basic_usage() {
        println!("\n=== Matrix Chain Multiplication ===");
        
        // 定义矩阵维度
        // A1: 10×30, A2: 30×5, A3: 5×60
        let dims = vec![10, 30, 5, 60];
        
        println!("Matrix dimensions:");
        for i in 0..dims.len()-1 {
            println!("  A{}: {} × {}", i+1, dims[i], dims[i+1]);
        }
        
        let mut mc = MatrixChain::new(dims);
        let _min_cost = mc.solve();
        let solution = mc.get_solution();
        
        println!("\n{}", solution);
        
        println!("\nCost Table:");
        println!("{}", mc.print_dp_table());
    }

    #[test]
    fn comparison_example() {
        println!("\n=== Comparison of Different Orders ===");
        
        let dims = vec![10, 30, 5, 60];
        
        // 方式1: (A1 × A2) × A3
        let cost1 = 10 * 30 * 5 + 10 * 5 * 60;
        println!("Order 1: (A1 × A2) × A3");
        println!("  Step 1: A1 × A2 = 10×30×5 = {}", 10 * 30 * 5);
        println!("  Step 2: Result × A3 = 10×5×60 = {}", 10 * 5 * 60);
        println!("  Total: {}", cost1);
        
        // 方式2: A1 × (A2 × A3)
        let cost2 = 30 * 5 * 60 + 10 * 30 * 60;
        println!("\nOrder 2: A1 × (A2 × A3)");
        println!("  Step 1: A2 × A3 = 30×5×60 = {}", 30 * 5 * 60);
        println!("  Step 2: A1 × Result = 10×30×60 = {}", 10 * 30 * 60);
        println!("  Total: {}", cost2);
        
        let mut mc = MatrixChain::new(dims);
        let optimal = mc.solve();
        println!("\nOptimal cost: {}", optimal);
        println!("Savings: {} operations", cost2 - optimal);
    }

    #[test]
    fn image_processing_example() {
        println!("\n=== Image Processing Chain Example ===");
        
        // 图像处理流水线中的矩阵变换
        // 例如：缩放、旋转、投影变换等
        let transforms = vec![
            ("Scale", "800×600 → 400×300"),
            ("Rotate", "400×300 → 400×300"),
            ("Project", "400×300 → 640×480"),
            ("Crop", "640×480 → 320×240"),
        ];
        
        println!("Transform chain:");
        for (name, desc) in &transforms {
            println!("  {}: {}", name, desc);
        }
        
        // 对应的维度链
        let dims = vec![800, 600, 400, 300, 640, 480, 320, 240];
        
        let mut mc = MatrixChain::new(dims);
        let _cost = mc.solve();
        let solution = mc.get_solution();
        
        println!("\nOptimal computation order:");
        println!("{}", solution);
    }
}
