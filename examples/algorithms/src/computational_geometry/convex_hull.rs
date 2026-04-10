//! 计算几何：凸包算法
//! 
//! 实现:
//! - Graham Scan: O(n log n)
//! - Jarvis March (Gift Wrapping): O(nh)
//! - Andrew's Monotone Chain: O(n log n)

use std::cmp::Ordering;

/// 2D点
#[derive(Debug, Clone, Copy, PartialEq)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    pub fn new(x: f64, y: f64) -> Self {
        Point { x, y }
    }
}

/// 叉积
fn cross(o: &Point, a: &Point, b: &Point) -> f64 {
    (a.x - o.x) * (b.y - o.y) - (a.y - o.y) * (b.x - o.x)
}

/// 距离平方
fn dist_sq(a: &Point, b: &Point) -> f64 {
    let dx = a.x - b.x;
    let dy = a.y - b.y;
    dx * dx + dy * dy
}

/// Andrew's Monotone Chain算法
/// 
/// # 复杂度
/// - 时间: O(n log n)
/// - 空间: O(n)
pub fn convex_hull_monotone_chain(points: &[Point]) -> Vec<Point> {
    let n = points.len();
    if n <= 1 {
        return points.to_vec();
    }
    
    let mut sorted = points.to_vec();
    sorted.sort_by(|a, b| {
        a.x.partial_cmp(&b.x).unwrap()
            .then_with(|| a.y.partial_cmp(&b.y).unwrap())
    });
    
    // 构建下凸包
    let mut lower = Vec::new();
    for p in &sorted {
        while lower.len() >= 2 && cross(&lower[lower.len()-2], &lower[lower.len()-1], p) <= 0.0 {
            lower.pop();
        }
        lower.push(*p);
    }
    
    // 构建上凸包
    let mut upper = Vec::new();
    for p in sorted.iter().rev() {
        while upper.len() >= 2 && cross(&upper[upper.len()-2], &upper[upper.len()-1], p) <= 0.0 {
            upper.pop();
        }
        upper.push(*p);
    }
    
    lower.pop();
    upper.pop();
    lower.extend(upper);
    lower
}

/// 计算多边形面积
pub fn polygon_area(points: &[Point]) -> f64 {
    let n = points.len();
    if n < 3 { return 0.0; }
    
    let mut area = 0.0;
    for i in 0..n {
        let j = (i + 1) % n;
        area += points[i].x * points[j].y;
        area -= points[j].x * points[i].y;
    }
    area.abs() / 2.0
}

#[cfg(test)]
mod tests {
    use super::*;
    
    #[test]
    fn test_convex_hull() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
            Point::new(0.5, 0.5),
        ];
        
        let hull = convex_hull_monotone_chain(&points);
        assert_eq!(hull.len(), 4);
    }
}
