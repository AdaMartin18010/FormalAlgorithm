//! LUP 分解（Lower-Upper Permutation Decomposition）
//!
//! 将方阵 A 分解为 P·A = L·U，其中：
//! - P 为置换矩阵（记录行交换）
//! - L 为单位下三角矩阵
//! - U 为上三角矩阵
//!
//! LUP 分解是求解线性方程组、计算矩阵行列式和求逆矩阵的核心工具。
//! 对标：CLRS Chapter 28.3

use crate::AlgorithmError;

/// LUP 分解结果
#[derive(Debug, Clone)]
pub struct LupResult {
    /// 下三角矩阵 L（对角线为 1）
    pub l: Vec<Vec<f64>>,
    /// 上三角矩阵 U
    pub u: Vec<Vec<f64>>,
    /// 置换数组： permutation[i] 表示第 i 行被替换为原矩阵的哪一行
    pub permutation: Vec<usize>,
}

impl LupResult {
    /// 利用 LUP 分解求解线性方程组 A·x = b
    ///
    /// 算法步骤：
    /// 1. 前向替换：求解 L·y = P·b
    /// 2. 后向替换：求解 U·x = y
    pub fn solve(&self, b: &[f64]) -> Result<Vec<f64>, AlgorithmError> {
        let n = self.u.len();
        if b.len() != n {
            return Err(AlgorithmError::InvalidInput(
                "b length must match matrix dimension".to_string(),
            ));
        }

        // 计算 P·b
        let mut pb = vec![0.0; n];
        for i in 0..n {
            pb[i] = b[self.permutation[i]];
        }

        // 前向替换：L·y = P·b
        let mut y = vec![0.0; n];
        for i in 0..n {
            let mut sum = pb[i];
            for j in 0..i {
                sum -= self.l[i][j] * y[j];
            }
            y[i] = sum; // L[i][i] == 1
        }

        // 后向替换：U·x = y
        let mut x = vec![0.0; n];
        for i in (0..n).rev() {
            let mut sum = y[i];
            for j in (i + 1)..n {
                sum -= self.u[i][j] * x[j];
            }
            if self.u[i][i].abs() < 1e-12 {
                return Err(AlgorithmError::InvalidInput(
                    "Singular matrix cannot be solved".to_string(),
                ));
            }
            x[i] = sum / self.u[i][i];
        }

        Ok(x)
    }

    /// 计算矩阵行列式
    pub fn determinant(&self) -> f64 {
        let mut det = 1.0;
        let n = self.u.len();
        for i in 0..n {
            det *= self.u[i][i];
        }
        // 根据置换次数调整符号
        let _swaps = 0usize;
        let mut visited = vec![false; n];
        for i in 0..n {
            if !visited[i] {
                let mut j = i;
                while self.permutation[j] != i {
                    j = self.permutation[j];
                    visited[j] = true;
                }
                visited[i] = true;
            }
        }
        // 更简单的符号计算：统计 inversion 的奇偶性
        let mut inversions = 0;
        for i in 0..n {
            for j in (i + 1)..n {
                if self.permutation[i] > self.permutation[j] {
                    inversions += 1;
                }
            }
        }
        if inversions % 2 == 1 {
            det = -det;
        }
        det
    }
}

/// LUP 分解
///
/// # 参数
/// * `a` - n×n 方阵（按值传入，内部会被修改）
///
/// # 返回值
/// 成功返回 `LupResult`，失败返回错误（非方阵或奇异矩阵）
///
/// # 示例
/// ```
/// use formal_algorithms::lup_decomposition::lup_decompose;
///
/// let a = vec![
///     vec![2.0, 0.0, 2.0],
///     vec![1.0, 1.0, 1.0],
///     vec![0.0, 2.0, 1.0],
/// ];
/// let lup = lup_decompose(a).unwrap();
/// let x = lup.solve(&vec![4.0, 3.0, 5.0]).unwrap();
/// // 验证 A·x = b
/// ```
pub fn lup_decompose(mut a: Vec<Vec<f64>>) -> Result<LupResult, AlgorithmError> {
    let n = a.len();
    if n == 0 {
        return Err(AlgorithmError::InvalidInput(
            "Matrix must be non-empty".to_string(),
        ));
    }
    for row in &a {
        if row.len() != n {
            return Err(AlgorithmError::InvalidInput(
                "Matrix must be square".to_string(),
            ));
        }
    }

    let mut permutation: Vec<usize> = (0..n).collect();

    for k in 0..n {
        // 选主元：找到第 k 列中绝对值最大的元素
        let mut pivot = k;
        let mut max_val = a[k][k].abs();
        for i in (k + 1)..n {
            if a[i][k].abs() > max_val {
                max_val = a[i][k].abs();
                pivot = i;
            }
        }

        if max_val < 1e-12 {
            return Err(AlgorithmError::InvalidInput(
                "Matrix is singular or nearly singular".to_string(),
            ));
        }

        // 交换第 k 行和第 pivot 行
        if pivot != k {
            a.swap(k, pivot);
            permutation.swap(k, pivot);
        }

        // 计算 U 的第 k 行和 L 的第 k 列
        for i in (k + 1)..n {
            a[i][k] /= a[k][k];
            for j in (k + 1)..n {
                a[i][j] -= a[i][k] * a[k][j];
            }
        }
    }

    // 分离 L 和 U
    let mut l = vec![vec![0.0; n]; n];
    let mut u = vec![vec![0.0; n]; n];
    for i in 0..n {
        l[i][i] = 1.0;
        for j in 0..i {
            l[i][j] = a[i][j];
        }
        for j in i..n {
            u[i][j] = a[i][j];
        }
    }

    Ok(LupResult { l, u, permutation })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_lup_basic() {
        let a = vec![
            vec![2.0, 3.0, 1.0],
            vec![4.0, 7.0, 2.0],
            vec![6.0, 18.0, 5.0],
        ];
        let lup = lup_decompose(a).unwrap();

        // 验证 L 是单位下三角
        for i in 0..3 {
            assert!((lup.l[i][i] - 1.0).abs() < 1e-9);
            for j in (i + 1)..3 {
                assert!(lup.l[i][j].abs() < 1e-9);
            }
        }
        // 验证 U 是上三角
        for i in 0..3 {
            for j in 0..i {
                assert!(lup.u[i][j].abs() < 1e-9);
            }
        }
    }

    #[test]
    fn test_solve_linear_system() {
        let a = vec![
            vec![1.0, 2.0, 0.0],
            vec![3.0, 4.0, 4.0],
            vec![5.0, 6.0, 3.0],
        ];
        let b = vec![3.0, 7.0, 8.0];
        let lup = lup_decompose(a).unwrap();
        let x = lup.solve(&b).unwrap();

        // 回代验证：实际解为 x = -1.4, y = 2.2, z = 0.6
        let expected = vec![-1.4, 2.2, 0.6];
        for i in 0..3 {
            assert!((x[i] - expected[i]).abs() < 1e-9);
        }
    }

    #[test]
    fn test_determinant() {
        let a = vec![
            vec![1.0, 2.0, 3.0],
            vec![0.0, 1.0, 4.0],
            vec![5.0, 6.0, 0.0],
        ];
        let lup = lup_decompose(a).unwrap();
        let det = lup.determinant();
        // 真实行列式 = 1
        assert!((det - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_singular_matrix() {
        let a = vec![
            vec![1.0, 2.0, 3.0],
            vec![2.0, 4.0, 6.0],
            vec![3.0, 6.0, 9.0],
        ];
        assert!(lup_decompose(a).is_err());
    }
}
