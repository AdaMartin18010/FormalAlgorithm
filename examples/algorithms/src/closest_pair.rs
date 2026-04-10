//! 最近点对算法 (Closest Pair of Points)
//!
//! 在平面上给定点集，找出距离最近的两个点。
//! 使用分治算法可以在O(n log n)时间内解决。
//!
//! # 算法复杂度
//! - 暴力算法: O(n²)
//! - 分治算法: O(n log n)
//! - 空间复杂度: O(n)
//!
//! # 算法思想
//! 1. 按x坐标排序所有点
//! 2. 递归地将点集分成左右两半
//! 3. 分别求解左右两半的最近点对
//! 4. 检查跨越中线的点对，只考虑距离中线不超过δ的点
//! 5. 对于每个点，只需检查y坐标排序后相邻的最多6个点

/// 二维点结构体
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    /// 创建新点
    pub fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// 计算两点之间的欧几里得距离
    ///
    /// # 复杂度
    /// - 时间复杂度: O(1)
    pub fn distance(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        (dx * dx + dy * dy).sqrt()
    }

    /// 计算两点之间的欧几里得距离的平方
    ///
    /// 避免开方运算，用于比较距离大小
    pub fn distance_squared(&self, other: &Point) -> f64 {
        let dx = self.x - other.x;
        let dy = self.y - other.y;
        dx * dx + dy * dy
    }
}

/// 最近点对结果
#[derive(Debug, Clone)]
pub struct ClosestPairResult {
    /// 第一个点
    pub p1: Point,
    /// 第二个点
    pub p2: Point,
    /// 最小距离
    pub distance: f64,
}

impl ClosestPairResult {
    fn new(p1: Point, p2: Point, distance: f64) -> Self {
        Self { p1, p2, distance }
    }
}

/// 使用暴力算法求解最近点对
///
/// # 参数
/// - `points`: 点集
///
/// # 返回
/// - 最近点对及其距离
///
/// # 复杂度
/// - 时间复杂度: O(n²)
/// - 空间复杂度: O(1)
pub fn closest_pair_brute_force(points: &[Point]) -> Option<ClosestPairResult> {
    let n = points.len();
    if n < 2 {
        return None;
    }

    let mut min_dist = f64::INFINITY;
    let mut result = None;

    for i in 0..n {
        for j in (i + 1)..n {
            let dist = points[i].distance(&points[j]);
            if dist < min_dist {
                min_dist = dist;
                result = Some(ClosestPairResult::new(points[i], points[j], dist));
            }
        }
    }

    result
}

/// 使用分治算法求解最近点对
///
/// # 参数
/// - `points`: 点集
///
/// # 返回
/// - 最近点对及其距离
///
/// # 复杂度
/// - 时间复杂度: O(n log n)
/// - 空间复杂度: O(n)
pub fn closest_pair(points: &[Point]) -> Option<ClosestPairResult> {
    let n = points.len();
    if n < 2 {
        return None;
    }

    // 点集太小，使用暴力算法
    if n <= 3 {
        return closest_pair_brute_force(points);
    }

    // 按x坐标排序
    let mut points_by_x: Vec<Point> = points.to_vec();
    points_by_x.sort_by(|a, b| a.x.partial_cmp(&b.x).unwrap());

    // 按y坐标排序（用于跨区域的检查）
    let mut points_by_y: Vec<Point> = points.to_vec();
    points_by_y.sort_by(|a, b| a.y.partial_cmp(&b.y).unwrap());

    closest_pair_recursive(&points_by_x, &points_by_y)
}

/// 分治算法的递归实现
///
/// # 参数
/// - `px`: 按x坐标排序的点集
/// - `py`: 按y坐标排序的点集
fn closest_pair_recursive(px: &[Point], py: &[Point]) -> Option<ClosestPairResult> {
    let n = px.len();

    // 基本情况：使用暴力算法
    if n <= 3 {
        return closest_pair_brute_force(px);
    }

    // 找到中点
    let mid = n / 2;
    let mid_point = px[mid];

    // 分割点集
    let mut left_py: Vec<Point> = Vec::with_capacity(mid);
    let mut right_py: Vec<Point> = Vec::with_capacity(n - mid);

    for &p in py {
        if p.x < mid_point.x || (p.x == mid_point.x && p.y <= mid_point.y) {
            if left_py.len() < mid {
                left_py.push(p);
            } else {
                right_py.push(p);
            }
        } else {
            right_py.push(p);
        }
    }

    // 递归求解左右两半
    let left_result = closest_pair_recursive(&px[..mid], &left_py);
    let right_result = closest_pair_recursive(&px[mid..], &right_py);

    // 取左右两边的最小值
    let mut best = match (&left_result, &right_result) {
        (Some(l), Some(r)) => {
            if l.distance < r.distance {
                left_result.clone()
            } else {
                right_result.clone()
            }
        }
        (Some(_), None) => left_result.clone(),
        (None, Some(_)) => right_result.clone(),
        (None, None) => None,
    };

    let delta = best.as_ref().map(|r| r.distance).unwrap_or(f64::INFINITY);

    // 检查跨越中线的点对
    let strip: Vec<Point> = py
        .iter()
        .filter(|&&p| (p.x - mid_point.x).abs() < delta)
        .copied()
        .collect();

    // 对于strip中的每个点，只需检查y坐标相近的最多6个点
    for i in 0..strip.len() {
        for j in (i + 1)..strip.len().min(i + 7) {
            // 如果y方向距离已经超过delta，停止检查
            if (strip[j].y - strip[i].y) >= delta {
                break;
            }

            let dist = strip[i].distance(&strip[j]);
            if dist < delta {
                best = Some(ClosestPairResult::new(strip[i], strip[j], dist));
            }
        }
    }

    best
}

/// 生成随机点集（用于测试）
#[cfg(test)]
pub fn generate_random_points(n: usize, seed: u64) -> Vec<Point> {
    use std::collections::hash_map::DefaultHasher;
    use std::hash::{Hash, Hasher};

    let mut points = Vec::with_capacity(n);
    let mut hasher = DefaultHasher::new();
    seed.hash(&mut hasher);
    let mut state = hasher.finish();

    for _ in 0..n {
        // 简单的伪随机数生成
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let x = ((state >> 32) as f64) / u32::MAX as f64 * 100.0;
        
        state = state.wrapping_mul(6364136223846793005).wrapping_add(1);
        let y = ((state >> 32) as f64) / u32::MAX as f64 * 100.0;
        
        points.push(Point::new(x, y));
    }

    points
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_two_points() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(3.0, 4.0),
        ];
        let result = closest_pair(&points).unwrap();
        assert_eq!(result.distance, 5.0);
    }

    #[test]
    fn test_simple_case() {
        let points = vec![
            Point::new(2.0, 3.0),
            Point::new(12.0, 30.0),
            Point::new(40.0, 50.0),
            Point::new(5.0, 1.0),
            Point::new(12.0, 10.0),
            Point::new(3.0, 4.0),
        ];
        
        let result = closest_pair(&points).unwrap();
        // 最近点对是 (2,3) 和 (3,4)，距离为 sqrt(2)
        assert!((result.distance - 2.0_f64.sqrt()).abs() < 1e-9);
    }

    #[test]
    fn test_duplicate_points() {
        let points = vec![
            Point::new(1.0, 1.0),
            Point::new(1.0, 1.0), // 重复点
            Point::new(100.0, 100.0),
        ];
        
        let result = closest_pair(&points).unwrap();
        assert_eq!(result.distance, 0.0);
    }

    #[test]
    fn test_collinear_points() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(3.0, 0.0),
            Point::new(100.0, 0.0),
        ];
        
        let result = closest_pair(&points).unwrap();
        assert_eq!(result.distance, 1.0);
    }

    #[test]
    fn test_less_than_two_points() {
        let points: Vec<Point> = vec![];
        assert!(closest_pair(&points).is_none());
        
        let points = vec![Point::new(1.0, 1.0)];
        assert!(closest_pair(&points).is_none());
    }

    #[test]
    fn test_brute_force_vs_divide_conquer() {
        let points = generate_random_points(100, 42);
        
        let brute_force = closest_pair_brute_force(&points).unwrap();
        let divide_conquer = closest_pair(&points).unwrap();
        
        assert!((brute_force.distance - divide_conquer.distance).abs() < 1e-9);
    }

    #[test]
    fn test_large_random_set() {
        let points = generate_random_points(1000, 12345);
        
        let start = std::time::Instant::now();
        let result = closest_pair(&points).unwrap();
        let elapsed = start.elapsed();
        
        println!("1000个点用时: {:?}", elapsed);
        assert!(result.distance >= 0.0);
    }

    #[test]
    fn test_vertical_line() {
        let points = vec![
            Point::new(5.0, 0.0),
            Point::new(5.0, 1.0),
            Point::new(5.0, 10.0),
            Point::new(5.0, 100.0),
        ];
        
        let result = closest_pair(&points).unwrap();
        assert_eq!(result.distance, 1.0);
    }

    #[test]
    fn test_horizontal_line() {
        let points = vec![
            Point::new(0.0, 5.0),
            Point::new(1.0, 5.0),
            Point::new(10.0, 5.0),
            Point::new(100.0, 5.0),
        ];
        
        let result = closest_pair(&points).unwrap();
        assert_eq!(result.distance, 1.0);
    }
}

/// 使用示例模块
pub mod examples {
    use super::*;

    /// 示例1: 基本用法
    pub fn example_basic() {
        println!("=== 最近点对算法基本用法 ===");
        
        let points = vec![
            Point::new(2.0, 3.0),
            Point::new(12.0, 30.0),
            Point::new(40.0, 50.0),
            Point::new(5.0, 1.0),
            Point::new(12.0, 10.0),
            Point::new(3.0, 4.0),
        ];
        
        println!("点集:");
        for (i, p) in points.iter().enumerate() {
            println!("  P{}: ({}, {})", i, p.x, p.y);
        }
        
        if let Some(result) = closest_pair(&points) {
            println!("\n最近点对:");
            println!("  点1: ({}, {})", result.p1.x, result.p1.y);
            println!("  点2: ({}, {})", result.p2.x, result.p2.y);
            println!("  距离: {}", result.distance);
        }
    }

    /// 示例2: 性能对比
    pub fn example_performance_comparison() {
        println!("\n=== 性能对比: 暴力算法 vs 分治算法 ===");
        
        let sizes = vec![100, 500, 1000];
        
        for size in sizes {
            let points = generate_random_points(size, 42);
            
            // 暴力算法
            let start = std::time::Instant::now();
            let _brute = closest_pair_brute_force(&points);
            let brute_time = start.elapsed();
            
            // 分治算法
            let start = std::time::Instant::now();
            let _dc = closest_pair(&points);
            let dc_time = start.elapsed();
            
            println!("点数 = {}: 暴力算法 {:?}, 分治算法 {:?}", 
                size, brute_time, dc_time);
        }
    }

    /// 示例3: 实际应用 - 寻找距离最近的两个设施
    pub fn example_facility_location() {
        println!("\n=== 设施选址示例 ===");
        
        // 模拟城市中的商店位置
        let stores = vec![
            Point::new(10.0, 20.0),  // 商店A
            Point::new(15.0, 25.0),  // 商店B
            Point::new(80.0, 90.0),  // 商店C
            Point::new(11.0, 21.0),  // 商店D
            Point::new(50.0, 50.0),  // 商店E
        ];
        
        println!("商店位置:");
        let names = vec!["A", "B", "C", "D", "E"];
        for (i, (p, name)) in stores.iter().zip(names.iter()).enumerate() {
            println!("  商店{}: ({}, {})", name, p.x, p.y);
        }
        
        if let Some(result) = closest_pair(&stores) {
            println!("\n距离最近的两个商店相距 {} 单位", result.distance);
            println!("建议考虑合并或差异化经营以避免直接竞争");
        }
    }
}
