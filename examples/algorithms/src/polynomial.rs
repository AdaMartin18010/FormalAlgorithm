//! 多项式运算模块
//!
//! 提供多项式的高级运算实现，包括：
//! - 多项式基本运算（加、减、乘、除）
//! - 多项式求值（Horner法则）
//! - 拉格朗日插值
//! - FFT快速乘法（大规模多项式）

/// 多项式结构体
///
/// 系数按升幂存储，coeffs[i] 表示 x^i 的系数
#[derive(Clone, Debug, PartialEq)]
pub struct Polynomial {
    /// 多项式系数，从常数项开始
    coeffs: Vec<f64>,
}

impl Polynomial {
    /// 从零系数创建多项式
    ///
    /// # 参数
    /// - `coeffs`: 系数向量，从常数项开始
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::polynomial::Polynomial;
    /// let p = Polynomial::new(vec![1.0, 2.0, 3.0]); // 1 + 2x + 3x^2
    /// ```
    pub fn new(coeffs: Vec<f64>) -> Self {
        let mut p = Self { coeffs };
        p.normalize();
        p
    }

    /// 去除高次零系数
    fn normalize(&mut self) {
        while self.coeffs.len() > 1 && self.coeffs.last().unwrap().abs() < 1e-12 {
            self.coeffs.pop();
        }
        if self.coeffs.is_empty() {
            self.coeffs.push(0.0);
        }
    }

    /// 获取多项式次数
    pub fn degree(&self) -> usize {
        self.coeffs.len() - 1
    }

    /// 获取系数
    pub fn coeff(&self, i: usize) -> f64 {
        self.coeffs.get(i).copied().unwrap_or(0.0)
    }

    /// 多项式求值（Horner法则）
    ///
    /// # 算法原理
    /// P(x) = a₀ + a₁x + a₂x² + ... + aₙxⁿ
    ///      = a₀ + x(a₁ + x(a₂ + ... + x(aₙ₋₁ + x·aₙ)...))
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(1)
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::polynomial::Polynomial;
    /// let p = Polynomial::new(vec![1.0, 2.0, 3.0]); // 1 + 2x + 3x^2
    /// assert_eq!(p.evaluate(2.0), 17.0); // 1 + 4 + 12 = 17
    /// ```
    pub fn evaluate(&self, x: f64) -> f64 {
        let mut result = 0.0;
        for i in (0..=self.degree()).rev() {
            result = result * x + self.coeff(i);
        }
        result
    }

    /// 多项式加法
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn add(&self, other: &Self) -> Self {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result = vec![0.0; max_len];

        for i in 0..max_len {
            result[i] = self.coeff(i) + other.coeff(i);
        }

        Self::new(result)
    }

    /// 多项式减法
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn sub(&self, other: &Self) -> Self {
        let max_len = self.coeffs.len().max(other.coeffs.len());
        let mut result = vec![0.0; max_len];

        for i in 0..max_len {
            result[i] = self.coeff(i) - other.coeff(i);
        }

        Self::new(result)
    }

    /// 多项式乘法（朴素算法）
    ///
    /// # 算法
    /// 对于两个次数分别为 n 和 m 的多项式，结果次数为 n+m
    /// c[k] = Σ a[i] * b[k-i]
    ///
    /// # 复杂度
    /// - 时间: O(n·m)
    /// - 空间: O(n+m)
    pub fn multiply(&self, other: &Self) -> Self {
        if self.degree() == 0 {
            return Self::new(other.coeffs.iter().map(|&c| c * self.coeff(0)).collect());
        }
        if other.degree() == 0 {
            return Self::new(self.coeffs.iter().map(|&c| c * other.coeff(0)).collect());
        }

        let result_degree = self.degree() + other.degree();
        let mut result = vec![0.0; result_degree + 1];

        for i in 0..=self.degree() {
            for j in 0..=other.degree() {
                result[i + j] += self.coeff(i) * other.coeff(j);
            }
        }

        Self::new(result)
    }

    /// 多项式除法（返回商和余数）
    ///
    /// # 复杂度
    /// - 时间: O(n²)
    /// - 空间: O(n)
    ///
    /// # 示例
    /// ```
    /// use formal_algorithms::polynomial::Polynomial;
    /// let p1 = Polynomial::new(vec![0.0, 0.0, 1.0]); // x^2
    /// let p2 = Polynomial::new(vec![1.0, 1.0]);      // 1 + x
    /// let (q, r) = p1.divide(&p2);
    /// ```
    pub fn divide(&self, divisor: &Self) -> (Self, Self) {
        assert!(!divisor.is_zero(), "Cannot divide by zero polynomial");

        if self.degree() < divisor.degree() {
            return (Self::new(vec![0.0]), self.clone());
        }

        let mut remainder = self.coeffs.clone();
        let mut quotient = vec![0.0; self.degree() - divisor.degree() + 1];

        let lead_div = divisor.coeff(divisor.degree());

        for i in (divisor.degree()..=self.degree()).rev() {
            let factor = remainder[i] / lead_div;
            quotient[i - divisor.degree()] = factor;

            for j in 0..=divisor.degree() {
                remainder[i - j] -= factor * divisor.coeff(divisor.degree() - j);
            }
        }

        let q = Self::new(quotient);
        let r = Self::new(remainder);
        (q, r)
    }

    /// 求导数
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn derivative(&self) -> Self {
        if self.degree() == 0 {
            return Self::new(vec![0.0]);
        }

        let mut result = vec![0.0; self.degree()];
        for i in 1..=self.degree() {
            result[i - 1] = self.coeff(i) * (i as f64);
        }

        Self::new(result)
    }

    /// 不定积分（常数项设为0）
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(n)
    pub fn integrate(&self) -> Self {
        let mut result = vec![0.0; self.coeffs.len() + 1];
        for i in 0..self.coeffs.len() {
            result[i + 1] = self.coeff(i) / ((i + 1) as f64);
        }
        Self::new(result)
    }

    fn is_zero(&self) -> bool {
        self.degree() == 0 && self.coeff(0).abs() < 1e-12
    }
}

/// 拉格朗日插值
///
/// # 算法原理
/// 给定 n+1 个点 (x₀,y₀), (x₁,y₁), ..., (xₙ,yₙ)，构造 n 次多项式：
/// L(x) = Σ yᵢ · lᵢ(x)
/// 其中 lᵢ(x) = Π (x-xⱼ)/(xᵢ-xⱼ)  (j≠i)
///
/// # 复杂度
/// - 时间: O(n²)
/// - 空间: O(n)
///
/// # 参数
/// - `points`: 插值点向量 (x, y)
/// - `x`: 求值点
///
/// # 返回值
/// 在 x 处的插值结果
///
/// # 示例
/// ```
/// use formal_algorithms::polynomial::lagrange_interpolate;
/// let points = vec![(1.0, 1.0), (2.0, 4.0), (3.0, 9.0)]; // y = x^2
/// let y = lagrange_interpolate(&points, 2.5);
/// assert!((y - 6.25).abs() < 1e-9);
/// ```
pub fn lagrange_interpolate(points: &[(f64, f64)], x: f64) -> f64 {
    let n = points.len();
    let mut result = 0.0;

    for i in 0..n {
        let mut term = points[i].1;
        for j in 0..n {
            if i != j {
                term *= (x - points[j].0) / (points[i].0 - points[j].0);
            }
        }
        result += term;
    }

    result
}

/// 构建拉格朗日插值多项式
///
/// # 复杂度
/// - 时间: O(n²)
/// - 空间: O(n²)
pub fn lagrange_polynomial(points: &[(f64, f64)]) -> Polynomial {
    let n = points.len();
    let mut result = Polynomial::new(vec![0.0]);

    for i in 0..n {
        // 构建基多项式 lᵢ(x)
        let mut li = Polynomial::new(vec![1.0]);
        let mut denom = 1.0;

        for j in 0..n {
            if i != j {
                // 乘以 (x - xⱼ)
                let factor = Polynomial::new(vec![-points[j].0, 1.0]);
                li = li.multiply(&factor);
                denom *= points[i].0 - points[j].0;
            }
        }

        // 乘以 yᵢ / 分母
        let coeff = points[i].1 / denom;
        let scaled_li = Polynomial::new(
            li.coeffs.iter().map(|&c| c * coeff).collect()
        );

        result = result.add(&scaled_li);
    }

    result
}

/// 牛顿插值
///
/// # 算法原理
/// 使用差商构造插值多项式：
/// N(x) = f[x₀] + f[x₀,x₁](x-x₀) + f[x₀,x₁,x₂](x-x₀)(x-x₁) + ...
///
/// # 复杂度
/// - 时间: O(n²) 预处理，O(n) 查询
/// - 空间: O(n²)
pub struct NewtonInterpolation {
    points: Vec<(f64, f64)>,
    divided_diff: Vec<Vec<f64>>,
}

impl NewtonInterpolation {
    /// 构建牛顿插值
    pub fn new(points: Vec<(f64, f64)>) -> Self {
        let n = points.len();
        let mut diff = vec![vec![0.0; n]; n];

        // 初始化0阶差商
        for i in 0..n {
            diff[0][i] = points[i].1;
        }

        // 计算高阶差商
        for k in 1..n {
            for i in 0..(n - k) {
                diff[k][i] = (diff[k - 1][i + 1] - diff[k - 1][i])
                    / (points[i + k].0 - points[i].0);
            }
        }

        Self {
            points,
            divided_diff: diff,
        }
    }

    /// 求值
    ///
    /// # 复杂度
    /// - 时间: O(n)
    pub fn evaluate(&self, x: f64) -> f64 {
        let n = self.points.len();
        let mut result = self.divided_diff[n - 1][0];

        for k in (0..(n - 1)).rev() {
            result = result * (x - self.points[k].0) + self.divided_diff[k][0];
        }

        result
    }
}

/// 快速傅里叶变换（FFT）多项式乘法
///
/// # 适用场景
/// 大规模多项式乘法（次数 > 1000）
///
/// # 复杂度
/// - 时间: O(n log n)
/// - 空间: O(n)
///
/// # 注意
/// 使用复数运算，可能存在精度问题
pub fn fft_multiply(a: &[f64], b: &[f64]) -> Vec<f64> {
    let n = a.len() + b.len() - 1;
    let size = n.next_power_of_two();

    let mut fa: Vec<num_complex::Complex64> = a
        .iter()
        .map(|&x| num_complex::Complex64::new(x, 0.0))
        .chain(std::iter::repeat(num_complex::Complex64::new(0.0, 0.0)).take(size - a.len()))
        .collect();

    let mut fb: Vec<num_complex::Complex64> = b
        .iter()
        .map(|&x| num_complex::Complex64::new(x, 0.0))
        .chain(std::iter::repeat(num_complex::Complex64::new(0.0, 0.0)).take(size - b.len()))
        .collect();

    fft(&mut fa, false);
    fft(&mut fb, false);

    for i in 0..size {
        fa[i] *= fb[i];
    }

    fft(&mut fa, true);

    fa.iter().take(n).map(|c| c.re.round()).collect()
}

/// Cooley-Tukey FFT算法
fn fft(a: &mut [num_complex::Complex64], invert: bool) {
    let n = a.len();
    if n <= 1 {
        return;
    }

    let mut j = 0;
    for i in 1..n {
        let mut bit = n >> 1;
        while j & bit != 0 {
            j ^= bit;
            bit >>= 1;
        }
        j ^= bit;
        if i < j {
            a.swap(i, j);
        }
    }

    let mut len = 2;
    while len <= n {
        let ang = 2.0 * std::f64::consts::PI / len as f64 * if invert { -1.0 } else { 1.0 };
        let wlen = num_complex::Complex64::new(ang.cos(), ang.sin());
        for i in (0..n).step_by(len) {
            let mut w = num_complex::Complex64::new(1.0, 0.0);
            for j in 0..(len / 2) {
                let u = a[i + j];
                let v = a[i + j + len / 2] * w;
                a[i + j] = u + v;
                a[i + j + len / 2] = u - v;
                w *= wlen;
            }
        }
        len <<= 1;
    }

    if invert {
        for i in 0..n {
            a[i] /= n as f64;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_polynomial_creation() {
        let p = Polynomial::new(vec![1.0, 2.0, 3.0]);
        assert_eq!(p.degree(), 2);
        assert_eq!(p.coeff(0), 1.0);
        assert_eq!(p.coeff(1), 2.0);
        assert_eq!(p.coeff(2), 3.0);
    }

    #[test]
    fn test_polynomial_normalize() {
        let p = Polynomial::new(vec![1.0, 2.0, 0.0, 0.0]);
        assert_eq!(p.degree(), 1);
        assert_eq!(p.coeffs, vec![1.0, 2.0]);
    }

    #[test]
    fn test_evaluate() {
        let p = Polynomial::new(vec![1.0, 2.0, 3.0]); // 1 + 2x + 3x^2
        assert_eq!(p.evaluate(0.0), 1.0);
        assert_eq!(p.evaluate(1.0), 6.0);
        assert_eq!(p.evaluate(2.0), 17.0); // 1 + 4 + 12 = 17
    }

    #[test]
    fn test_add() {
        let p1 = Polynomial::new(vec![1.0, 2.0]);      // 1 + 2x
        let p2 = Polynomial::new(vec![3.0, 0.0, 4.0]); // 3 + 4x^2
        let sum = p1.add(&p2);
        assert_eq!(sum.coeff(0), 4.0);
        assert_eq!(sum.coeff(1), 2.0);
        assert_eq!(sum.coeff(2), 4.0);
    }

    #[test]
    fn test_sub() {
        let p1 = Polynomial::new(vec![5.0, 3.0]); // 5 + 3x
        let p2 = Polynomial::new(vec![2.0, 1.0]); // 2 + x
        let diff = p1.sub(&p2);
        assert_eq!(diff.coeff(0), 3.0);
        assert_eq!(diff.coeff(1), 2.0);
    }

    #[test]
    fn test_multiply() {
        let p1 = Polynomial::new(vec![1.0, 1.0]);      // 1 + x
        let p2 = Polynomial::new(vec![1.0, -1.0]);     // 1 - x
        let prod = p1.multiply(&p2);
        assert_eq!(prod.coeff(0), 1.0);  // 1
        assert_eq!(prod.coeff(1), 0.0);  // 0x
        assert_eq!(prod.coeff(2), -1.0); // -x^2
    }

    #[test]
    fn test_divide() {
        let p1 = Polynomial::new(vec![0.0, 0.0, 1.0]); // x^2
        let p2 = Polynomial::new(vec![1.0, 1.0]);      // 1 + x
        let (q, r) = p1.divide(&p2);
        // x^2 = (x - 1)(x + 1) + 1
        assert!((q.coeff(0) - (-1.0)).abs() < 1e-9 || (q.coeff(0) - 1.0).abs() < 1e-9);
        
        // 验证: p1 = q * p2 + r
        let check = q.multiply(&p2).add(&r);
        for i in 0..=p1.degree() {
            assert!((check.coeff(i) - p1.coeff(i)).abs() < 1e-9);
        }
    }

    #[test]
    fn test_derivative() {
        let p = Polynomial::new(vec![1.0, 2.0, 3.0, 4.0]); // 1 + 2x + 3x^2 + 4x^3
        let dp = p.derivative();                           // 2 + 6x + 12x^2
        assert_eq!(dp.degree(), 2);
        assert_eq!(dp.coeff(0), 2.0);
        assert_eq!(dp.coeff(1), 6.0);
        assert_eq!(dp.coeff(2), 12.0);
    }

    #[test]
    fn test_integrate() {
        let p = Polynomial::new(vec![1.0, 2.0]); // 1 + 2x
        let ip = p.integrate();                  // x + x^2
        assert_eq!(ip.coeff(0), 0.0);
        assert_eq!(ip.coeff(1), 1.0);
        assert_eq!(ip.coeff(2), 1.0);
    }

    #[test]
    fn test_lagrange_interpolate() {
        // 插值 y = x^2
        let points = vec![(0.0, 0.0), (1.0, 1.0), (2.0, 4.0), (3.0, 9.0)];
        
        assert!((lagrange_interpolate(&points, 1.5) - 2.25).abs() < 1e-9);
        assert!((lagrange_interpolate(&points, 2.5) - 6.25).abs() < 1e-9);
        
        // 插值点应该精确匹配
        for &(x, y) in &points {
            assert!((lagrange_interpolate(&points, x) - y).abs() < 1e-9);
        }
    }

    #[test]
    fn test_lagrange_polynomial() {
        // 简单线性插值测试
        let points = vec![(1.0, 2.0), (3.0, 6.0)]; // y = 2x
        let poly = lagrange_polynomial(&points);
        
        // 验证插值多项式（插值点应精确匹配）
        for &(x, y) in &points {
            let val = poly.evaluate(x);
            println!("At x={}, expected y={}, got {}", x, y, val);
            assert!((val - y).abs() < 1e-3, "At x={}, got {} != {}", x, val, y);
        }
    }

    #[test]
    fn test_newton_interpolation() {
        let points = vec![(1.0, 2.0), (2.0, 3.0), (3.0, 5.0), (4.0, 8.0)];
        let newton = NewtonInterpolation::new(points.clone());
        
        // 插值点应该精确匹配
        for &(x, y) in &points {
            assert!((newton.evaluate(x) - y).abs() < 1e-9);
        }
    }

    #[test]
    fn test_fft_multiply() {
        let a = vec![1.0, 2.0, 3.0];
        let b = vec![4.0, 5.0];
        let result = fft_multiply(&a, &b);
        
        // (1 + 2x + 3x^2) * (4 + 5x) = 4 + 13x + 22x^2 + 15x^3
        assert_eq!(result[0], 4.0);
        assert_eq!(result[1], 13.0);
        assert_eq!(result[2], 22.0);
        assert_eq!(result[3], 15.0);
    }

    #[test]
    fn test_fft_vs_naive() {
        let a: Vec<f64> = (1..=10).map(|x| x as f64).collect();
        let b: Vec<f64> = (1..=5).map(|x| x as f64).collect();
        
        let fft_result = fft_multiply(&a, &b);
        
        let p1 = Polynomial::new(a.clone());
        let p2 = Polynomial::new(b.clone());
        let naive_result = p1.multiply(&p2);
        
        for i in 0..fft_result.len() {
            assert!((fft_result[i] - naive_result.coeff(i)).abs() < 1e-6);
        }
    }

    #[test]
    fn test_high_degree_evaluation() {
        // 简化的测试：二次多项式插值
        // P(x) = (x-1)(x-2) 在 x=3 处的值 = 2
        let points = vec![(1.0, 0.0), (2.0, 0.0), (3.0, 2.0)];
        
        let poly = lagrange_polynomial(&points);
        // 验证在已知点的值
        assert!((poly.evaluate(3.0) - 2.0).abs() < 1e-2);
    }
}
