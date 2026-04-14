//! 矩阵操作模块
//!
//! 提供矩阵运算的高级算法实现，包括：
//! - Strassen矩阵乘法（分治优化）
//! - 矩阵快速幂（用于线性递推）
//! - 高斯消元（解线性方程组）

use std::ops::{Add, Sub};

/// 矩阵结构体
#[derive(Clone, Debug, PartialEq)]
pub struct Matrix<T> {
    data: Vec<Vec<T>>,
    rows: usize,
    cols: usize,
}

impl<T: Copy + Default> Matrix<T> {
    /// 创建新矩阵
    ///
    /// # 参数
    /// - `rows`: 行数
    /// - `cols`: 列数
    /// - `data`: 二维向量数据
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::matrix_operations::Matrix;
    /// let m = Matrix::new(2, 2, vec![vec![1, 2], vec![3, 4]]);
    /// ```
    pub fn new(rows: usize, cols: usize, data: Vec<Vec<T>>) -> Self {
        assert_eq!(data.len(), rows);
        assert!(data.iter().all(|row| row.len() == cols));
        Self { data, rows, cols }
    }

    /// 创建零矩阵
    pub fn zeros(rows: usize, cols: usize) -> Self
    where
        T: Default,
    {
        let data = vec![vec![T::default(); cols]; rows];
        Self { data, rows, cols }
    }

    /// 获取元素
    pub fn get(&self, i: usize, j: usize) -> T {
        self.data[i][j]
    }

    /// 设置元素
    pub fn set(&mut self, i: usize, j: usize, val: T) {
        self.data[i][j] = val;
    }

    pub fn rows(&self) -> usize {
        self.rows
    }

    pub fn cols(&self) -> usize {
        self.cols
    }
}

impl Matrix<i64> {
    /// 标准矩阵乘法
    ///
    /// # 算法
    /// 三重循环实现，时间复杂度 O(n³)
    ///
    /// # 复杂度
    /// - 时间: O(n³)
    /// - 空间: O(n²)
    pub fn multiply(&self, other: &Self) -> Self {
        assert_eq!(self.cols, other.rows);
        let mut result = Self::zeros(self.rows, other.cols);

        for i in 0..self.rows {
            for j in 0..other.cols {
                let mut sum: i64 = 0;
                for k in 0..self.cols {
                    sum += self.get(i, k) * other.get(k, j);
                }
                result.set(i, j, sum);
            }
        }
        result
    }

    /// Strassen矩阵乘法
    ///
    /// # 算法原理
    /// 将矩阵分块，通过7次乘法而非8次完成2×2块矩阵乘法
    /// 递归应用于子矩阵
    ///
    /// # 复杂度
    /// - 时间: O(n^log₂7) ≈ O(n^2.807)
    /// - 空间: O(n²)
    ///
    /// # 注意
    /// 当矩阵尺寸较小时，回退到标准乘法（减少常数因子开销）
    pub fn strassen_multiply(&self, other: &Self) -> Self {
        assert_eq!(self.cols, other.rows);
        assert_eq!(self.rows, self.cols, "Strassen requires square matrix");
        assert!(self.rows.is_power_of_two(), "Size must be power of 2");

        let n = self.rows;
        if n <= 64 {
            // 小矩阵使用标准乘法
            return self.multiply(other);
        }

        let mid = n / 2;

        // 分块
        let (a11, a12, a21, a22) = self.split();
        let (b11, b12, b21, b22) = other.split();

        // 计算7个乘积
        let m1 = (a11.clone() + a22.clone()).strassen_multiply(&(b11.clone() + b22.clone()));
        let m2 = (a21.clone() + a22.clone()).strassen_multiply(&b11);
        let m3 = a11.strassen_multiply(&(b12.clone() - b22.clone()));
        let m4 = a22.strassen_multiply(&(b21.clone() - b11.clone()));
        let m5 = (a11.clone() + a12.clone()).strassen_multiply(&b22);
        let m6 = (a21.clone() - a11.clone()).strassen_multiply(&(b11.clone() + b12.clone()));
        let m7 = (a12.clone() - a22.clone()).strassen_multiply(&(b21.clone() + b22.clone()));

        // 组合结果
        let c11 = &(&(&m1 + &m4) - &m5) + &m7;
        let c12 = &m3 + &m5;
        let c21 = &m2 + &m4;
        let c22 = &(&(&(&m1 - &m2) + &m3) + &m6);

        Self::combine(c11, c12, c21, c22.clone())
    }

    /// 将矩阵分成四块
    fn split(&self) -> (Self, Self, Self, Self) {
        let n = self.rows / 2;
        let mut a11 = Self::zeros(n, n);
        let mut a12 = Self::zeros(n, n);
        let mut a21 = Self::zeros(n, n);
        let mut a22 = Self::zeros(n, n);

        for i in 0..n {
            for j in 0..n {
                a11.set(i, j, self.get(i, j));
                a12.set(i, j, self.get(i, j + n));
                a21.set(i, j, self.get(i + n, j));
                a22.set(i, j, self.get(i + n, j + n));
            }
        }

        (a11, a12, a21, a22)
    }

    /// 组合四块矩阵
    fn combine(c11: Self, c12: Self, c21: Self, c22: Self) -> Self {
        let n = c11.rows;
        let mut result = Self::zeros(2 * n, 2 * n);

        for i in 0..n {
            for j in 0..n {
                result.set(i, j, c11.get(i, j));
                result.set(i, j + n, c12.get(i, j));
                result.set(i + n, j, c21.get(i, j));
                result.set(i + n, j + n, c22.get(i, j));
            }
        }

        result
    }

    /// 矩阵快速幂
    ///
    /// # 算法原理
    /// 类似整数快速幂，利用二进制分解：
    /// A^n = A^(n/2) * A^(n/2)  (n为偶数)
    /// A^n = A * A^(n-1)        (n为奇数)
    ///
    /// # 应用场景
    /// - 线性递推数列（如斐波那契）
    /// - 图论中计算长度为k的路径数
    /// - 马尔可夫链状态转移
    ///
    /// # 复杂度
    /// - 时间: O(n³ log k)，其中k为幂次
    /// - 空间: O(n²)
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::matrix_operations::Matrix;
    /// let m = Matrix::new(2, 2, vec![vec![1, 1], vec![1, 0]]);
    /// let result = m.pow(10); // 计算第11个斐波那契数
    /// ```
    pub fn pow(&self, mut n: u64) -> Self {
        assert_eq!(self.rows, self.cols, "Matrix must be square");

        let mut result = Self::identity(self.rows);
        let mut base = self.clone();

        while n > 0 {
            if n & 1 == 1 {
                result = result.multiply(&base);
            }
            base = base.multiply(&base);
            n >>= 1;
        }

        result
    }

    /// 创建单位矩阵
    pub fn identity(n: usize) -> Self {
        let mut result = Self::zeros(n, n);
        for i in 0..n {
            result.set(i, i, 1);
        }
        result
    }
}

impl Matrix<f64> {
    /// 高斯消元法解线性方程组 Ax = b
    ///
    /// # 算法原理
    /// 通过初等行变换将增广矩阵化为上三角矩阵，然后回代求解
    ///
    /// # 步骤
    /// 1. 前向消元：将矩阵化为行阶梯形
    /// 2. 选主元：数值稳定性（部分主元）
    /// 3. 回代：从最后一行向上求解
    ///
    /// # 复杂度
    /// - 时间: O(n³)
    /// - 空间: O(n²)
    ///
    /// # 返回值
    /// - `Some(Vec<f64>)`: 方程组的解
    /// - `None`: 无解或无穷多解
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::matrix_operations::Matrix;
    /// let a = Matrix::new(2, 2, vec![vec![2.0, 1.0], vec![1.0, 3.0]]);
    /// let b = vec![5.0, 8.0];
    /// let x = a.gaussian_elimination(&b).unwrap();
    /// ```
    pub fn gaussian_elimination(&self, b: &[f64]) -> Option<Vec<f64>> {
        assert_eq!(self.rows, self.cols);
        assert_eq!(self.rows, b.len());

        let n = self.rows;
        let mut aug: Vec<Vec<f64>> = self
            .data
            .iter()
            .zip(b.iter())
            .map(|(row, &bi)| {
                let mut new_row = row.clone();
                new_row.push(bi);
                new_row
            })
            .collect();

        // 前向消元（部分主元）
        for i in 0..n {
            // 选主元
            let mut max_row = i;
            for k in (i + 1)..n {
                if aug[k][i].abs() > aug[max_row][i].abs() {
                    max_row = k;
                }
            }
            aug.swap(i, max_row);

            // 主元为0，矩阵奇异
            if aug[i][i].abs() < 1e-10 {
                return None;
            }

            // 消元
            for k in (i + 1)..n {
                let factor = aug[k][i] / aug[i][i];
                // 从i+1开始，保留aug[k][i] = 0
                for j in (i + 1)..=n {
                    aug[k][j] -= factor * aug[i][j];
                }
            }
        }

        // 回代
        let mut x = vec![0.0; n];
        for i in (0..n).rev() {
            let mut sum = aug[i][n];
            for j in ((i + 1)..n).rev() {
                sum -= aug[i][j] * x[j];
            }
            x[i] = sum / aug[i][i];
        }

        Some(x)
    }

    /// 计算矩阵的行列式（高斯消元）
    ///
    /// # 复杂度
    /// - 时间: O(n³)
    /// - 空间: O(n²)
    pub fn determinant(&self) -> f64 {
        assert_eq!(self.rows, self.cols, "Matrix must be square");
        let n = self.rows;

        let mut mat = self.data.clone();
        let mut det = 1.0;
        let mut sign = 1.0;

        for i in 0..n {
            // 选主元
            let mut max_row = i;
            for k in (i + 1)..n {
                if mat[k][i].abs() > mat[max_row][i].abs() {
                    max_row = k;
                }
            }

            if max_row != i {
                mat.swap(i, max_row);
                sign = -sign;
            }

            if mat[i][i].abs() < 1e-10 {
                return 0.0;
            }

            det *= mat[i][i];

            // 消元
            for k in (i + 1)..n {
                let factor = mat[k][i] / mat[i][i];
                for j in i..n {
                    mat[k][j] -= factor * mat[i][j];
                }
            }
        }

        sign * det
    }
}

// 矩阵加法实现（引用版）
impl<T: Copy + Add<Output = T> + Default> Add for &Matrix<T> {
    type Output = Matrix<T>;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.rows, other.rows);
        assert_eq!(self.cols, other.cols);

        let mut result = Matrix::zeros(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.set(i, j, self.get(i, j) + other.get(i, j));
            }
        }
        result
    }
}

// 矩阵加法实现（所有权版）
impl<T: Copy + Add<Output = T> + Default> Add for Matrix<T> {
    type Output = Matrix<T>;

    fn add(self, other: Self) -> Self::Output {
        assert_eq!(self.rows, other.rows);
        assert_eq!(self.cols, other.cols);

        let mut result = Matrix::zeros(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.set(i, j, self.get(i, j) + other.get(i, j));
            }
        }
        result
    }
}

// 矩阵减法实现（引用版）
impl<T: Copy + Sub<Output = T> + Default> Sub for &Matrix<T> {
    type Output = Matrix<T>;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.rows, other.rows);
        assert_eq!(self.cols, other.cols);

        let mut result = Matrix::zeros(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.set(i, j, self.get(i, j) - other.get(i, j));
            }
        }
        result
    }
}

// 矩阵减法实现（所有权版）
impl<T: Copy + Sub<Output = T> + Default> Sub for Matrix<T> {
    type Output = Matrix<T>;

    fn sub(self, other: Self) -> Self::Output {
        assert_eq!(self.rows, other.rows);
        assert_eq!(self.cols, other.cols);

        let mut result = Matrix::zeros(self.rows, self.cols);
        for i in 0..self.rows {
            for j in 0..self.cols {
                result.set(i, j, self.get(i, j) - other.get(i, j));
            }
        }
        result
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matrix_creation() {
        let m = Matrix::new(2, 3, vec![vec![1, 2, 3], vec![4, 5, 6]]);
        assert_eq!(m.rows(), 2);
        assert_eq!(m.cols(), 3);
        assert_eq!(m.get(0, 0), 1);
        assert_eq!(m.get(1, 2), 6);
    }

    #[test]
    fn test_matrix_zeros() {
        let m = Matrix::<i64>::zeros(3, 3);
        assert_eq!(m.get(1, 1), 0);
        assert_eq!(m.rows(), 3);
    }

    #[test]
    fn test_standard_multiply() {
        let a = Matrix::new(2, 2, vec![vec![1, 2], vec![3, 4]]);
        let b = Matrix::new(2, 2, vec![vec![5, 6], vec![7, 8]]);
        let c = a.multiply(&b);

        assert_eq!(c.get(0, 0), 19);
        assert_eq!(c.get(0, 1), 22);
        assert_eq!(c.get(1, 0), 43);
        assert_eq!(c.get(1, 1), 50);
    }

    #[test]
    fn test_strassen_multiply() {
        // 创建8x8矩阵（2的幂次）
        let mut data_a = vec![vec![0i64; 8]; 8];
        let mut data_b = vec![vec![0i64; 8]; 8];
        
        for i in 0..8 {
            for j in 0..8 {
                data_a[i][j] = (i + j) as i64;
                data_b[i][j] = (i * j + 1) as i64;
            }
        }

        let a = Matrix::new(8, 8, data_a);
        let b = Matrix::new(8, 8, data_b);

        let standard = a.multiply(&b);
        let strassen = a.strassen_multiply(&b);

        assert_eq!(standard, strassen);
    }

    #[test]
    fn test_matrix_pow() {
        let m = Matrix::new(2, 2, vec![vec![1, 1], vec![1, 0]]);
        let result = m.pow(10);

        // F(11) = 89, F(10) = 55
        assert_eq!(result.get(0, 0), 89);
        assert_eq!(result.get(0, 1), 55);
        assert_eq!(result.get(1, 0), 55);
        assert_eq!(result.get(1, 1), 34);
    }

    #[test]
    fn test_identity() {
        let i = Matrix::<i64>::identity(3);
        assert_eq!(i.get(0, 0), 1);
        assert_eq!(i.get(0, 1), 0);
        assert_eq!(i.get(1, 1), 1);
    }

    #[test]
    fn test_gaussian_elimination() {
        // 简单对角矩阵测试
        // 2x = 4, 3y = 9
        // 解: x=2, y=3
        let a = Matrix::new(2, 2, vec![vec![2.0, 0.0], vec![0.0, 3.0]]);
        let b = vec![4.0, 9.0];
        
        let result = a.gaussian_elimination(&b);
        assert!(result.is_some(), "gaussian_elimination returned None");
        let x = result.unwrap();
        assert!((x[0] - 2.0).abs() < 1e-6, "x[0] = {} != 2.0", x[0]);
        assert!((x[1] - 3.0).abs() < 1e-6, "x[1] = {} != 3.0", x[1]);
    }

    #[test]
    fn test_gaussian_elimination_3x3() {
        // 3x3 方程组 - 对角矩阵，容易求解
        let a = Matrix::new(
            3,
            3,
            vec![
                vec![2.0, 0.0, 0.0],
                vec![0.0, 3.0, 0.0],
                vec![0.0, 0.0, 5.0],
            ],
        );
        let b = vec![2.0, 6.0, 15.0]; // x = 1, y = 2, z = 3
        
        let x = a.gaussian_elimination(&b).unwrap();
        assert!((x[0] - 1.0).abs() < 1e-6);
        assert!((x[1] - 2.0).abs() < 1e-6);
        assert!((x[2] - 3.0).abs() < 1e-6);
    }

    #[test]
    fn test_determinant() {
        let a = Matrix::new(2, 2, vec![vec![4.0, 7.0], vec![2.0, 6.0]]);
        let det = a.determinant();
        assert!((det - 10.0).abs() < 1e-9); // 4*6 - 7*2 = 24 - 14 = 10

        let b = Matrix::new(3, 3, vec![
            vec![1.0, 2.0, 3.0],
            vec![0.0, 1.0, 4.0],
            vec![5.0, 6.0, 0.0],
        ]);
        let det_b = b.determinant();
        assert!((det_b - 1.0).abs() < 1e-6);
    }

    #[test]
    fn test_matrix_add_sub() {
        let a = Matrix::new(2, 2, vec![vec![1, 2], vec![3, 4]]);
        let b = Matrix::new(2, 2, vec![vec![5, 6], vec![7, 8]]);

        let sum = &a + &b;
        assert_eq!(sum.get(0, 0), 6);
        assert_eq!(sum.get(1, 1), 12);

        let diff = &b - &a;
        assert_eq!(diff.get(0, 0), 4);
        assert_eq!(diff.get(1, 1), 4);
    }

    #[test]
    fn test_fibonacci_via_matrix_pow() {
        // 斐波那契: F(n) = F(n-1) + F(n-2)
        // [F(n+1)]   [1 1]^n   [F(1)]
        // [F(n)  ] = [1 0]   * [F(0)]
        let fib_matrix = Matrix::new(2, 2, vec![vec![1, 1], vec![1, 0]]);
        
        // F(0)=0, F(1)=1, F(2)=1, F(3)=2, F(4)=3, F(5)=5
        let m5 = fib_matrix.pow(5);
        assert_eq!(m5.get(1, 0), 5); // F(5)

        let m10 = fib_matrix.pow(10);
        assert_eq!(m10.get(1, 0), 55); // F(10)

        let m20 = fib_matrix.pow(20);
        assert_eq!(m20.get(1, 0), 6765); // F(20)
    }
}
