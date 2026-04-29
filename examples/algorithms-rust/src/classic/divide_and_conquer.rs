//! 分治算法框架与实现
//!
//! 分治算法(Divide and Conquer)将问题分解为若干子问题，递归解决后合并结果。
//! 本模块包含经典的分治算法实现：矩阵乘法(Strassen算法)、最近点对问题。

use crate::{AlgorithmError, SearchResult};

/// 二维点结构
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    /// x坐标
    pub x: f64,
    /// y坐标
    pub y: f64,
}

impl Point {
    /// 创建新点
    ///
    /// # 示例
    ///
    /// ```
    /// use formal_algorithms::divide_and_conquer::Point;
    ///
    /// let p = Point::new(1.0, 2.0);
    /// assert_eq!(p.x, 1.0);
    /// assert_eq!(p.y, 2.0);
    /// ```
    pub fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }

    /// 计算两点间欧几里得距离的平方
    ///
    /// 避免开方运算，用于比较距离大小
    pub fn distance_squared(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        dx * dx + dy * dy
    }

    /// 计算两点间欧几里得距离
    pub fn distance(&self, other: &Point) -> f64 {
        self.distance_squared(other).sqrt()
    }
}

/// 矩阵乘法结果
#[derive(Debug, Clone, PartialEq)]
pub struct Matrix {
    /// 矩阵数据，按行存储
    pub data: Vec<Vec<i64>>,
    /// 行数
    pub rows: usize,
    /// 列数
    pub cols: usize,
}

impl Matrix {
    /// 创建新矩阵
    pub fn new(data: Vec<Vec<i64>>) -> Self {
        let rows = data.len();
        let cols = if rows > 0 { data[0].len() } else { 0 };
        Matrix { data, rows, cols }
    }

    /// 创建零矩阵
    pub fn zeros(rows: usize, cols: usize) -> Self {
        Matrix {
            data: vec![vec![0; cols]; rows],
            rows,
            cols,
        }
    }
}

/// 标准矩阵乘法
///
/// # 算法说明
///
/// 使用三重循环实现矩阵乘法：
/// C[i][j] = Σ(A[i][k] * B[k][j])
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n³)
/// - **空间复杂度**：O(n²)
///
/// # 参数
///
/// * `a` - 左矩阵，维度 m×n
/// * `b` - 右矩阵，维度 n×p
///
/// # 返回值
///
/// 返回结果矩阵，维度 m×p
///
/// # 示例
///
/// ```
/// use formal_algorithms::divide_and_conquer::{Matrix, matrix_multiply};
///
/// let a = Matrix::new(vec![
///     vec![1, 2],
///     vec![3, 4],
/// ]);
/// let b = Matrix::new(vec![
///     vec![5, 6],
///     vec![7, 8],
/// ]);
///
/// let c = matrix_multiply(&a, &b).unwrap();
/// assert_eq!(c.data, vec![
///     vec![19, 22],
///     vec![43, 50],
/// ]);
/// ```
pub fn matrix_multiply(a: &Matrix, b: &Matrix) -> SearchResult<Matrix> {
    if a.cols != b.rows {
        return Err(AlgorithmError::InvalidInput(
            "Matrix dimensions do not match for multiplication".to_string(),
        ));
    }

    let mut result = Matrix::zeros(a.rows, b.cols);

    for i in 0..a.rows {
        for j in 0..b.cols {
            let mut sum = 0i64;
            for k in 0..a.cols {
                sum += a.data[i][k] * b.data[k][j];
            }
            result.data[i][j] = sum;
        }
    }

    Ok(result)
}

/// Strassen矩阵乘法
///
/// 使用分治策略，将矩阵分成4个子矩阵递归相乘。
/// 通过巧妙的线性组合，将8次乘法减少到7次。
///
/// # 算法说明
///
/// 对于矩阵 A = [A11 A12; A21 A22], B = [B11 B12; B21 B22]
/// 计算7个中间矩阵 M1-M7，然后组合得到结果
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n^log₂7) ≈ O(n^2.807)
/// - **空间复杂度**：O(n²)
///
/// # 注意
///
/// 只有当矩阵维度为2的幂且较大时，Strassen算法才比标准算法快
///
/// # 示例
///
/// ```
/// use formal_algorithms::divide_and_conquer::{Matrix, strassen_multiply};
///
/// let a = Matrix::new(vec![
///     vec![1, 2, 3, 4],
///     vec![5, 6, 7, 8],
///     vec![9, 10, 11, 12],
///     vec![13, 14, 15, 16],
/// ]);
/// let b = Matrix::new(vec![
///     vec![1, 0, 0, 0],
///     vec![0, 1, 0, 0],
///     vec![0, 0, 1, 0],
///     vec![0, 0, 0, 1],
/// ]);
///
/// let c = strassen_multiply(&a, &b).unwrap();
/// // 乘以单位矩阵，结果应等于原矩阵
/// assert_eq!(c.data, a.data);
/// ```
pub fn strassen_multiply(a: &Matrix, b: &Matrix) -> SearchResult<Matrix> {
    if a.cols != b.rows {
        return Err(AlgorithmError::InvalidInput(
            "Matrix dimensions do not match".to_string(),
        ));
    }

    // 对于小矩阵，使用标准乘法
    if a.rows <= 64 || a.rows % 2 != 0 || b.cols % 2 != 0 {
        return matrix_multiply(a, b);
    }

    let n = a.rows;
    let _half = n / 2;

    // 分割矩阵
    let (a11, a12, a21, a22) = split_matrix(&a.data);
    let (b11, b12, b21, b22) = split_matrix(&b.data);

    // 计算7个中间矩阵
    let m1 = strassen_multiply(
        &Matrix::new(add_matrix(&a11, &a22)),
        &Matrix::new(add_matrix(&b11, &b22)),
    )?;
    let m2 = strassen_multiply(&Matrix::new(a21.clone()), &Matrix::new(add_matrix(&b11, &b12)))?;
    let m3 = strassen_multiply(&Matrix::new(add_matrix(&a11, &a12)), &Matrix::new(b22.clone()))?;
    let m4 = strassen_multiply(&Matrix::new(a22.clone()), &Matrix::new(sub_matrix(&b21, &b11)))?;
    let m5 = strassen_multiply(&Matrix::new(add_matrix(&a11, &a22)), &Matrix::new(b11.clone()))?;
    let m6 = strassen_multiply(
        &Matrix::new(sub_matrix(&a21, &a11)),
        &Matrix::new(add_matrix(&b11, &b12)),
    )?;
    let m7 = strassen_multiply(
        &Matrix::new(sub_matrix(&a12, &a22)),
        &Matrix::new(add_matrix(&b21, &b22)),
    )?;

    // 组合结果
    let c11 = add_matrix(&sub_matrix(&add_matrix(&m1.data, &m4.data), &m5.data), &m7.data);
    let c12 = add_matrix(&m3.data, &m5.data);
    let c21 = add_matrix(&m2.data, &m4.data);
    let c22 = add_matrix(
        &sub_matrix(&add_matrix(&m1.data, &m3.data), &m2.data),
        &m6.data,
    );

    Ok(Matrix::new(combine_matrix(&c11, &c12, &c21, &c22)))
}

/// 分割矩阵为4个子矩阵
fn split_matrix(mat: &[Vec<i64>]) -> (Vec<Vec<i64>>, Vec<Vec<i64>>, Vec<Vec<i64>>, Vec<Vec<i64>>) {
    let n = mat.len();
    let half = n / 2;

    let mut a11 = vec![vec![0; half]; half];
    let mut a12 = vec![vec![0; half]; half];
    let mut a21 = vec![vec![0; half]; half];
    let mut a22 = vec![vec![0; half]; half];

    for i in 0..half {
        for j in 0..half {
            a11[i][j] = mat[i][j];
            a12[i][j] = mat[i][j + half];
            a21[i][j] = mat[i + half][j];
            a22[i][j] = mat[i + half][j + half];
        }
    }

    (a11, a12, a21, a22)
}

/// 矩阵加法
fn add_matrix(a: &[Vec<i64>], b: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = a.len();
    let mut result = vec![vec![0; n]; n];
    for i in 0..n {
        for j in 0..n {
            result[i][j] = a[i][j] + b[i][j];
        }
    }
    result
}

/// 矩阵减法
fn sub_matrix(a: &[Vec<i64>], b: &[Vec<i64>]) -> Vec<Vec<i64>> {
    let n = a.len();
    let mut result = vec![vec![0; n]; n];
    for i in 0..n {
        for j in 0..n {
            result[i][j] = a[i][j] - b[i][j];
        }
    }
    result
}

/// 组合4个子矩阵
fn combine_matrix(
    c11: &[Vec<i64>],
    c12: &[Vec<i64>],
    c21: &[Vec<i64>],
    c22: &[Vec<i64>],
) -> Vec<Vec<i64>> {
    let n = c11.len();
    let mut result = vec![vec![0; 2 * n]; 2 * n];

    for i in 0..n {
        for j in 0..n {
            result[i][j] = c11[i][j];
            result[i][j + n] = c12[i][j];
            result[i + n][j] = c21[i][j];
            result[i + n][j + n] = c22[i][j];
        }
    }

    result
}

/// 最近点对问题
///
/// 在一组点中找到距离最近的两个点
///
/// # 算法说明
///
/// 使用分治策略：
/// 1. 按x坐标排序，将点集分为左右两半
/// 2. 递归求解左右子集的最近点对
/// 3. 检查跨越中线的点对
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(n log n)
/// - **空间复杂度**：O(n)
///
/// # 参数
///
/// * `points` - 点集
///
/// # 返回值
///
/// 返回最近点对的距离和点的索引
///
/// # 示例
///
/// ```
/// use formal_algorithms::divide_and_conquer::{Point, closest_pair};
///
/// let points = vec![
///     Point::new(2.0, 3.0),
///     Point::new(12.0, 30.0),
///     Point::new(40.0, 50.0),
///     Point::new(5.0, 1.0),
///     Point::new(12.0, 10.0),
///     Point::new(3.0, 4.0),
/// ];
///
/// let (min_dist, idx1, idx2) = closest_pair(&points);
/// // 最近点对是 (2,3) 和 (3,4)，距离为 √2 ≈ 1.414
/// assert!((min_dist - 2.0f64.sqrt()).abs() < 1e-10);
/// ```
pub fn closest_pair(points: &[Point]) -> (f64, usize, usize) {
    if points.len() < 2 {
        return (f64::INFINITY, 0, 0);
    }

    // 创建按x坐标排序的索引数组
    let mut px: Vec<usize> = (0..points.len()).collect();
    px.sort_by(|&i, &j| points[i].x.partial_cmp(&points[j].x).unwrap());

    // 创建按y坐标排序的索引数组
    let mut py: Vec<usize> = (0..points.len()).collect();
    py.sort_by(|&i, &j| points[i].y.partial_cmp(&points[j].y).unwrap());

    closest_pair_recursive(points, &px, &py)
}

/// 递归求解最近点对
fn closest_pair_recursive(
    points: &[Point],
    px: &[usize],
    py: &[usize],
) -> (f64, usize, usize) {
    let n = px.len();

    // 基本情况：暴力求解
    if n <= 3 {
        return brute_force(points, px);
    }

    let mid = n / 2;
    let mid_point = &points[px[mid]];

    // 分割
    let (plx, prx) = px.split_at(mid);

    // 按y坐标分割
    let mut ply: Vec<usize> = Vec::new();
    let mut pry: Vec<usize> = Vec::new();
    for &i in py {
        if points[i].x <= mid_point.x {
            ply.push(i);
        } else {
            pry.push(i);
        }
    }

    // 递归求解
    let (dl, il, jl) = closest_pair_recursive(points, plx, &ply);
    let (dr, ir, jr) = closest_pair_recursive(points, prx, &pry);

    // 取最小值
    let (mut d, mut i1, mut i2) = if dl < dr { (dl, il, jl) } else { (dr, ir, jr) };

    // 检查跨越中线的点对
    let mut strip: Vec<usize> = Vec::new();
    for &i in py {
        let dx = (points[i].x - mid_point.x).abs();
        if dx < d {
            strip.push(i);
        }
    }

    // 检查带内点对
    for i in 0..strip.len() {
        for j in (i + 1)..strip.len().min(i + 8) {
            let dist = points[strip[i]].distance(&points[strip[j]]);
            if dist < d {
                d = dist;
                i1 = strip[i];
                i2 = strip[j];
            }
        }
    }

    (d, i1, i2)
}

/// 暴力求解最近点对
fn brute_force(points: &[Point], indices: &[usize]) -> (f64, usize, usize) {
    let mut min_dist = f64::INFINITY;
    let mut i1 = indices[0];
    let mut i2 = indices[1];

    for i in 0..indices.len() {
        for j in (i + 1)..indices.len() {
            let dist = points[indices[i]].distance(&points[indices[j]]);
            if dist < min_dist {
                min_dist = dist;
                i1 = indices[i];
                i2 = indices[j];
            }
        }
    }

    (min_dist, i1, i2)
}

/// 二分查找（分治基础）
///
/// 在有序数组中查找元素的索引
///
/// # 算法说明
///
/// 将搜索区间不断减半，直到找到目标或区间为空
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(log n)
/// - **空间复杂度**：O(1)
///
/// # 示例
///
/// ```
/// use formal_algorithms::divide_and_conquer::binary_search_dc;
///
/// let arr = vec![1, 3, 5, 7, 9, 11, 13];
/// assert_eq!(binary_search_dc(&arr, 7), Some(3));
/// assert_eq!(binary_search_dc(&arr, 6), None);
/// ```
pub fn binary_search_dc<T: Ord>(arr: &[T], target: T) -> Option<usize> {
    binary_search_recursive(arr, &target, 0, arr.len())
}

fn binary_search_recursive<T: Ord>(
    arr: &[T],
    target: &T,
    left: usize,
    right: usize,
) -> Option<usize> {
    if left >= right {
        return None;
    }

    let mid = left + (right - left) / 2;

    match arr[mid].cmp(target) {
        std::cmp::Ordering::Equal => Some(mid),
        std::cmp::Ordering::Less => binary_search_recursive(arr, target, mid + 1, right),
        std::cmp::Ordering::Greater => {
            if mid == 0 {
                None
            } else {
                binary_search_recursive(arr, target, left, mid)
            }
        }
    }
}

/// 归并排序（分治经典）
///
/// # 示例
///
/// ```
/// use formal_algorithms::divide_and_conquer::merge_sort_dc;
///
/// let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
/// merge_sort_dc(&mut arr);
/// assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
/// ```
pub fn merge_sort_dc<T: Ord + Clone>(arr: &mut [T]) {
    if arr.len() <= 1 {
        return;
    }

    let len = arr.len();
    let mid = len / 2;

    merge_sort_dc(&mut arr[..mid]);
    merge_sort_dc(&mut arr[mid..]);

    let mut temp = arr.to_vec();
    merge(&arr[..mid], &arr[mid..], &mut temp);
    arr.clone_from_slice(&temp);
}

fn merge<T: Ord + Clone>(left: &[T], right: &[T], result: &mut [T]) {
    let (mut i, mut j, mut k) = (0, 0, 0);

    while i < left.len() && j < right.len() {
        if left[i] <= right[j] {
            result[k] = left[i].clone();
            i += 1;
        } else {
            result[k] = right[j].clone();
            j += 1;
        }
        k += 1;
    }

    while i < left.len() {
        result[k] = left[i].clone();
        i += 1;
        k += 1;
    }

    while j < right.len() {
        result[k] = right[j].clone();
        j += 1;
        k += 1;
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_matrix_multiply() {
        let a = Matrix::new(vec![
            vec![1, 2],
            vec![3, 4],
        ]);
        let b = Matrix::new(vec![
            vec![5, 6],
            vec![7, 8],
        ]);

        let c = matrix_multiply(&a, &b).unwrap();
        assert_eq!(c.data, vec![
            vec![19, 22],
            vec![43, 50],
        ]);
    }

    #[test]
    fn test_matrix_multiply_dimension_mismatch() {
        let a = Matrix::new(vec![vec![1, 2, 3]]);
        let b = Matrix::new(vec![vec![1, 2]]);

        assert!(matrix_multiply(&a, &b).is_err());
    }

    #[test]
    fn test_strassen_multiply() {
        let a = Matrix::new(vec![
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![9, 10, 11, 12],
            vec![13, 14, 15, 16],
        ]);
        let b = Matrix::new(vec![
            vec![1, 0, 0, 0],
            vec![0, 1, 0, 0],
            vec![0, 0, 1, 0],
            vec![0, 0, 0, 1],
        ]);

        let c = strassen_multiply(&a, &b).unwrap();
        assert_eq!(c.data, a.data);
    }

    #[test]
    fn test_strassen_vs_standard() {
        let a = Matrix::new(vec![
            vec![1, 2, 3, 4],
            vec![5, 6, 7, 8],
            vec![9, 10, 11, 12],
            vec![13, 14, 15, 16],
        ]);
        let b = Matrix::new(vec![
            vec![2, 0, 1, 3],
            vec![1, 2, 0, 1],
            vec![0, 1, 2, 0],
            vec![3, 0, 1, 2],
        ]);

        let standard = matrix_multiply(&a, &b).unwrap();
        let strassen = strassen_multiply(&a, &b).unwrap();
        assert_eq!(standard.data, strassen.data);
    }

    #[test]
    fn test_closest_pair() {
        let points = vec![
            Point::new(2.0, 3.0),
            Point::new(12.0, 30.0),
            Point::new(40.0, 50.0),
            Point::new(5.0, 1.0),
            Point::new(12.0, 10.0),
            Point::new(3.0, 4.0),
        ];

        let (min_dist, i, j) = closest_pair(&points);
        // 最近点对是 (2,3) 和 (3,4)，距离为 √2
        assert!((min_dist - 2.0f64.sqrt()).abs() < 1e-10);
        // 验证返回的索引
        assert!((i == 0 && j == 5) || (i == 5 && j == 0));
    }

    #[test]
    fn test_closest_pair_two_points() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(3.0, 4.0),
        ];

        let (min_dist, _i, _j) = closest_pair(&points);
        assert!((min_dist - 5.0).abs() < 1e-10);
    }

    #[test]
    fn test_closest_pair_single_point() {
        let points = vec![Point::new(0.0, 0.0)];
        let (min_dist, _, _) = closest_pair(&points);
        assert!(min_dist.is_infinite());
    }

    #[test]
    fn test_binary_search_dc() {
        let arr = vec![1, 3, 5, 7, 9, 11, 13];
        assert_eq!(binary_search_dc(&arr, 7), Some(3));
        assert_eq!(binary_search_dc(&arr, 1), Some(0));
        assert_eq!(binary_search_dc(&arr, 13), Some(6));
        assert_eq!(binary_search_dc(&arr, 6), None);
        assert_eq!(binary_search_dc(&arr, 0), None);
        assert_eq!(binary_search_dc(&arr, 14), None);
    }

    #[test]
    fn test_merge_sort_dc() {
        let mut arr = vec![64, 34, 25, 12, 22, 11, 90];
        merge_sort_dc(&mut arr);
        assert_eq!(arr, vec![11, 12, 22, 25, 34, 64, 90]);
    }

    #[test]
    fn test_merge_sort_dc_empty() {
        let mut arr: Vec<i32> = vec![];
        merge_sort_dc(&mut arr);
        assert!(arr.is_empty());
    }

    #[test]
    fn test_point_distance() {
        let p1 = Point::new(0.0, 0.0);
        let p2 = Point::new(3.0, 4.0);
        assert!((p1.distance(&p2) - 5.0).abs() < 1e-10);
        assert_eq!(p1.distance_squared(&p2), 25.0);
    }
}
