//! 几何工具模块
//!
//! 提供计算几何的基础数据结构和算法：
//! - 基础几何对象：点、线、圆、多边形
//! - 凸包算法（Graham扫描、Andrew算法）
//! - 旋转卡壳（直径、宽度、最小矩形）
//! - 几何判定和计算工具

pub use std::f64::consts::PI;

/// 二维点
#[derive(Clone, Copy, Debug, PartialEq, Default)]
pub struct Point {
    pub x: f64,
    pub y: f64,
}

impl Point {
    /// 创建新点
    pub const fn new(x: f64, y: f64) -> Self {
        Self { x, y }
    }

    /// 原点
    pub const fn origin() -> Self {
        Self { x: 0.0, y: 0.0 }
    }

    /// 向量加法
    pub fn add(&self, other: Self) -> Self {
        Self::new(self.x + other.x, self.y + other.y)
    }

    /// 向量减法
    pub fn sub(&self, other: Self) -> Self {
        Self::new(self.x - other.x, self.y - other.y)
    }

    /// 数乘
    pub fn mul(&self, k: f64) -> Self {
        Self::new(self.x * k, self.y * k)
    }

    /// 点积
    pub fn dot(&self, other: Self) -> f64 {
        self.x * other.x + self.y * other.y
    }

    /// 叉积（二维叉积返回标量）
    pub fn cross(&self, other: Self) -> f64 {
        self.x * other.y - self.y * other.x
    }

    /// 向量长度平方
    pub fn len_sq(&self) -> f64 {
        self.x * self.x + self.y * self.y
    }

    /// 向量长度
    pub fn len(&self) -> f64 {
        self.len_sq().sqrt()
    }

    /// 距离平方
    pub fn dist_sq(&self, other: Self) -> f64 {
        self.sub(other).len_sq()
    }

    /// 欧几里得距离
    pub fn dist(&self, other: Self) -> f64 {
        self.dist_sq(other).sqrt()
    }

    /// 单位向量
    pub fn normalize(&self) -> Self {
        let l = self.len();
        if l < 1e-12 {
            Self::origin()
        } else {
            self.mul(1.0 / l)
        }
    }

    /// 极角（范围 [-π, π]）
    pub fn angle(&self) -> f64 {
        self.y.atan2(self.x)
    }

    /// 绕原点旋转
    pub fn rotate(&self, theta: f64) -> Self {
        let cos_t = theta.cos();
        let sin_t = theta.sin();
        Self::new(
            self.x * cos_t - self.y * sin_t,
            self.x * sin_t + self.y * cos_t,
        )
    }

    /// 绕指定点旋转
    pub fn rotate_around(&self, center: Self, theta: f64) -> Self {
        self.sub(center).rotate(theta).add(center)
    }
}

/// 线段
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Segment {
    pub a: Point,
    pub b: Point,
}

impl Segment {
    /// 创建线段
    pub const fn new(a: Point, b: Point) -> Self {
        Self { a, b }
    }

    /// 线段长度
    pub fn len(&self) -> f64 {
        self.a.dist(self.b)
    }

    /// 线段中点
    pub fn midpoint(&self) -> Point {
        Point::new((self.a.x + self.b.x) / 2.0, (self.a.y + self.b.y) / 2.0)
    }

    /// 判断点是否在线段上（含端点）
    pub fn contains(&self, p: Point) -> bool {
        // 共线且在线段包围盒内
        let cross = (p.sub(self.a)).cross(self.b.sub(self.a));
        if cross.abs() > 1e-9 {
            return false;
        }
        let dot = (p.sub(self.a)).dot(p.sub(self.b));
        dot <= 1e-9
    }

    /// 线段相交判定
    pub fn intersect(&self, other: &Self) -> bool {
        // 快速排斥实验
        if self.a.x.max(self.b.x) < other.a.x.min(other.b.x)
            || self.a.x.min(self.b.x) > other.a.x.max(other.b.x)
            || self.a.y.max(self.b.y) < other.a.y.min(other.b.y)
            || self.a.y.min(self.b.y) > other.a.y.max(other.b.y)
        {
            return false;
        }

        // 跨立实验
        let d1 = (other.b.sub(other.a)).cross(self.a.sub(other.a));
        let d2 = (other.b.sub(other.a)).cross(self.b.sub(other.a));
        let d3 = (self.b.sub(self.a)).cross(other.a.sub(self.a));
        let d4 = (self.b.sub(self.a)).cross(other.b.sub(self.a));

        if d1 * d2 < -1e-9 && d3 * d4 < -1e-9 {
            return true;
        }

        // 检查端点是否在线段上
        if d1.abs() < 1e-9 && other.contains(self.a) {
            return true;
        }
        if d2.abs() < 1e-9 && other.contains(self.b) {
            return true;
        }
        if d3.abs() < 1e-9 && self.contains(other.a) {
            return true;
        }
        if d4.abs() < 1e-9 && self.contains(other.b) {
            return true;
        }

        false
    }

    /// 求线段交点
    pub fn intersection(&self, other: &Self) -> Option<Point> {
        if !self.intersect(other) {
            return None;
        }

        let d = (self.b.sub(self.a)).cross(other.b.sub(other.a));
        if d.abs() < 1e-9 {
            // 共线
            return None;
        }

        let t = (other.a.sub(self.a)).cross(other.b.sub(other.a)) / d;
        Some(self.a.add(self.b.sub(self.a).mul(t)))
    }
}

/// 直线（无限延伸）
#[derive(Clone, Copy, Debug)]
pub struct Line {
    pub a: f64, // Ax + By + C = 0
    pub b: f64,
    pub c: f64,
}

impl Line {
    /// 通过两点创建直线
    pub fn from_points(p1: Point, p2: Point) -> Self {
        let a = p2.y - p1.y;
        let b = p1.x - p2.x;
        let c = p2.x * p1.y - p1.x * p2.y;
        Self { a, b, c }
    }

    /// 通过点斜式创建
    pub fn from_point_slope(p: Point, slope: f64) -> Self {
        let a = slope;
        let b = -1.0;
        let c = p.y - slope * p.x;
        Self { a, b, c }
    }

    /// 点是否在直线上
    pub fn contains(&self, p: Point) -> bool {
        (self.a * p.x + self.b * p.y + self.c).abs() < 1e-9
    }

    /// 点到位直线距离
    pub fn distance_to(&self, p: Point) -> f64 {
        (self.a * p.x + self.b * p.y + self.c).abs()
            / (self.a * self.a + self.b * self.b).sqrt()
    }

    /// 两直线交点
    pub fn intersection(&self, other: &Self) -> Option<Point> {
        let det = self.a * other.b - self.b * other.a;
        if det.abs() < 1e-9 {
            return None; // 平行或重合
        }
        let x = (self.b * other.c - other.b * self.c) / det;
        let y = (other.a * self.c - self.a * other.c) / det;
        Some(Point::new(x, y))
    }
}

/// 圆
#[derive(Clone, Copy, Debug, PartialEq)]
pub struct Circle {
    pub center: Point,
    pub r: f64,
}

impl Circle {
    /// 创建圆
    pub const fn new(center: Point, r: f64) -> Self {
        Self { center, r }
    }

    /// 点在圆上/内/外判定
    /// 返回: -1=内, 0=上, 1=外
    pub fn point_position(&self, p: Point) -> i32 {
        let d2 = self.center.dist_sq(p);
        let r2 = self.r * self.r;
        if (d2 - r2).abs() < 1e-9 {
            0
        } else if d2 < r2 {
            -1
        } else {
            1
        }
    }

    /// 点是否在圆内（含边界）
    pub fn contains(&self, p: Point) -> bool {
        self.point_position(p) <= 0
    }

    /// 圆与圆的位置关系
    /// 返回: 0=相离, 1=外切, 2=相交, 3=内切, 4=内含, 5=重合
    pub fn relation(&self, other: &Self) -> i32 {
        let d = self.center.dist(other.center);
        let r_sum = self.r + other.r;
        let r_diff = (self.r - other.r).abs();

        if d < 1e-9 && (self.r - other.r).abs() < 1e-9 {
            return 5; // 重合
        }
        if (d - r_sum).abs() < 1e-9 {
            return 1; // 外切
        }
        if (d - r_diff).abs() < 1e-9 {
            return 3; // 内切
        }
        if d > r_sum {
            return 0; // 相离
        }
        if d < r_diff {
            return 4; // 内含
        }
        2 // 相交
    }

    /// 两圆交点
    pub fn intersections(&self, other: &Self) -> Vec<Point> {
        let mut result = vec![];
        let d = self.center.dist(other.center);
        let rel = self.relation(other);

        if rel == 0 || rel == 4 || rel == 5 {
            return result;
        }

        let a = (self.r * self.r - other.r * other.r + d * d) / (2.0 * d);
        let h_sq = self.r * self.r - a * a;

        if h_sq < -1e-9 {
            return result;
        }

        let h = h_sq.max(0.0).sqrt();
        let p2 = self.center.add(other.center.sub(self.center).mul(a / d));

        if h < 1e-9 {
            result.push(p2);
        } else {
            let dx = -(other.center.y - self.center.y) * (h / d);
            let dy = (other.center.x - self.center.x) * (h / d);
            result.push(Point::new(p2.x + dx, p2.y + dy));
            result.push(Point::new(p2.x - dx, p2.y - dy));
        }

        result
    }

    /// 最小覆盖圆（Welzl算法）
    ///
    /// # 复杂度
    /// - 期望时间: O(n)
    /// - 最坏时间: O(n⁴)（但概率极低）
    pub fn minimum_enclosing(points: &[Point]) -> Self {
        if points.is_empty() {
            return Self::new(Point::origin(), 0.0);
        }
        if points.len() == 1 {
            return Self::new(points[0], 0.0);
        }

        let mut p: Vec<Point> = points.to_vec();
        // Fisher-Yates 洗牌
        for i in (1..p.len()).rev() {
            let j = (i as f64 * rand::random::<f64>()) as usize % (i + 1);
            p.swap(i, j);
        }

        Self::welzl(&p, &[], 0)
    }

    fn welzl(p: &[Point], r: &[Point], idx: usize) -> Self {
        if idx == p.len() || r.len() == 3 {
            return Self::trivial(r);
        }

        let c = Self::welzl(p, r, idx + 1);
        if c.contains(p[idx]) {
            return c;
        }

        let mut r2 = r.to_vec();
        r2.push(p[idx]);
        Self::welzl(p, &r2, idx + 1)
    }

    fn trivial(r: &[Point]) -> Self {
        match r.len() {
            0 => Self::new(Point::origin(), 0.0),
            1 => Self::new(r[0], 0.0),
            2 => {
                let c = Segment::new(r[0], r[1]).midpoint();
                let radius = r[0].dist(c);
                Self::new(c, radius)
            }
            3 => {
                // 三点确定圆（外接圆）
                let a = r[0];
                let b = r[1];
                let c = r[2];
                
                let d = 2.0 * (a.x * (b.y - c.y) + b.x * (c.y - a.y) + c.x * (a.y - b.y));
                if d.abs() < 1e-9 {
                    // 三点共线，返回覆盖三点的最小圆
                    let ab = Self::trivial(&[a, b]);
                    let bc = Self::trivial(&[b, c]);
                    let ac = Self::trivial(&[a, c]);
                    let candidates = vec![ab, bc, ac];
                    candidates
                        .into_iter()
                        .filter(|circle| {
                            circle.contains(a) && circle.contains(b) && circle.contains(c)
                        })
                        .min_by(|a, b| a.r.partial_cmp(&b.r).unwrap())
                        .unwrap()
                } else {
                    let ux = ((a.x * a.x + a.y * a.y) * (b.y - c.y)
                        + (b.x * b.x + b.y * b.y) * (c.y - a.y)
                        + (c.x * c.x + c.y * c.y) * (a.y - b.y))
                        / d;
                    let uy = ((a.x * a.x + a.y * a.y) * (c.x - b.x)
                        + (b.x * b.x + b.y * b.y) * (a.x - c.x)
                        + (c.x * c.x + c.y * c.y) * (b.x - a.x))
                        / d;
                    let center = Point::new(ux, uy);
                    let radius = center.dist(a);
                    Self::new(center, radius)
                }
            }
            _ => unreachable!(),
        }
    }
}

/// 多边形
#[derive(Clone, Debug, PartialEq)]
pub struct Polygon {
    pub vertices: Vec<Point>,
}

impl Polygon {
    /// 从顶点创建多边形（按顺序）
    pub fn new(vertices: Vec<Point>) -> Self {
        Self { vertices }
    }

    /// 顶点数量
    pub fn len(&self) -> usize {
        self.vertices.len()
    }

    pub fn is_empty(&self) -> bool {
        self.vertices.is_empty()
    }

    /// 获取边
    pub fn edge(&self, i: usize) -> Segment {
        let n = self.len();
        Segment::new(self.vertices[i], self.vertices[(i + 1) % n])
    }

    /// 多边形面积（有向面积，正为逆时针）
    ///
    /// # 算法
    /// 鞋带公式：A = ½|Σ(xᵢ(yᵢ₊₁ - yᵢ₋₁))|
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(1)
    pub fn area(&self) -> f64 {
        let n = self.len();
        if n < 3 {
            return 0.0;
        }

        let mut area = 0.0;
        for i in 0..n {
            let j = (i + 1) % n;
            area += self.vertices[i].x * self.vertices[j].y;
            area -= self.vertices[j].x * self.vertices[i].y;
        }
        area.abs() / 2.0
    }

    /// 多边形周长
    pub fn perimeter(&self) -> f64 {
        let n = self.len();
        if n < 2 {
            return 0.0;
        }

        let mut perim = 0.0;
        for i in 0..n {
            perim += self.edge(i).len();
        }
        perim
    }

    /// 点在多边形内判定（射线法）
    ///
    /// # 复杂度
    /// - 时间: O(n)
    /// - 空间: O(1)
    pub fn contains(&self, p: Point) -> bool {
        let n = self.len();
        if n < 3 {
            return false;
        }

        let mut inside = false;
        for i in 0..n {
            let a = self.vertices[i];
            let b = self.vertices[(i + 1) % n];

            // 检查点是否在边上
            if Segment::new(a, b).contains(p) {
                return true;
            }

            // 射线交叉判定
            let intersect = ((a.y > p.y) != (b.y > p.y))
                && (p.x < (b.x - a.x) * (p.y - a.y) / (b.y - a.y) + a.x);
            if intersect {
                inside = !inside;
            }
        }
        inside
    }

    /// 多边形是否为凸
    pub fn is_convex(&self) -> bool {
        let n = self.len();
        if n < 3 {
            return false;
        }

        let mut has_pos = false;
        let mut has_neg = false;

        for i in 0..n {
            let a = self.vertices[i];
            let b = self.vertices[(i + 1) % n];
            let c = self.vertices[(i + 2) % n];

            let cross = b.sub(a).cross(c.sub(b));
            if cross > 1e-9 {
                has_pos = true;
            } else if cross < -1e-9 {
                has_neg = true;
            }

            if has_pos && has_neg {
                return false;
            }
        }
        true
    }
}

/// 计算凸包（Andrew单调链算法）
///
/// # 算法原理
/// 1. 按x坐标排序，x相同按y排序
/// 2. 构建下凸壳：从左到右，保持逆时针转向
/// 3. 构建上凸壳：从右到左，保持逆时针转向
///
/// # 复杂度
/// - 时间: O(n log n)（主要花费在排序）
/// - 空间: O(n)
///
/// # 返回值
/// 凸包顶点序列（逆时针，不含重复起点）
///
/// # 示例
/// ```
/// use formal_algorithms::geometry_utils::{convex_hull, Point};
/// let points = vec![
///     Point::new(0.0, 0.0), Point::new(1.0, 0.0),
///     Point::new(0.5, 0.5), Point::new(0.0, 1.0),
/// ];
/// let hull = convex_hull(&points);
/// ```
pub fn convex_hull(points: &[Point]) -> Vec<Point> {
    let n = points.len();
    if n <= 1 {
        return points.to_vec();
    }

    // 排序
    let mut pts: Vec<Point> = points.to_vec();
    pts.sort_by(|a, b| {
        a.x.partial_cmp(&b.x)
            .unwrap()
            .then_with(|| a.y.partial_cmp(&b.y).unwrap())
    });

    // 构建下凸壳
    let mut lower: Vec<Point> = vec![];
    for &p in &pts {
        while lower.len() >= 2 {
            let n = lower.len();
            let cross = lower[n - 1].sub(lower[n - 2]).cross(p.sub(lower[n - 1]));
            if cross <= 1e-9 {
                lower.pop();
            } else {
                break;
            }
        }
        lower.push(p);
    }

    // 构建上凸壳
    let mut upper: Vec<Point> = vec![];
    for &p in pts.iter().rev() {
        while upper.len() >= 2 {
            let n = upper.len();
            let cross = upper[n - 1].sub(upper[n - 2]).cross(p.sub(upper[n - 1]));
            if cross <= 1e-9 {
                upper.pop();
            } else {
                break;
            }
        }
        upper.push(p);
    }

    // 合并（去掉重复的端点）
    lower.pop();
    upper.pop();
    lower.extend(upper);
    lower
}

/// 凸包直径（旋转卡壳）
///
/// # 算法原理
/// 凸包上最远的两点一定在凸包的顶点对踵点对中
/// 使用旋转卡壳在O(n)时间内找到所有对踵点对
///
/// # 复杂度
/// - 时间: O(n)（假设已计算凸包）
/// - 空间: O(1)
pub fn rotating_calipers_diameter(hull: &[Point]) -> f64 {
    let n = hull.len();
    if n == 0 {
        return 0.0;
    }
    if n == 1 {
        return 0.0;
    }
    if n == 2 {
        return hull[0].dist(hull[1]);
    }

    // 找到y坐标最大的点（最上方）
    let mut k = 1;
    while k < n && hull[k].y >= hull[k - 1].y {
        k += 1;
    }
    k -= 1;

    let mut i = 0;
    let mut j = k;
    let mut max_dist = hull[i].dist_sq(hull[j]);

    while i <= k && j < n {
        let ni = (i + 1) % n;
        let nj = (j + 1) % n;

        // 比较两条边的斜率
        let cross = hull[ni].sub(hull[i]).cross(hull[nj].sub(hull[j]));
        if cross > 0.0 {
            i += 1;
        } else {
            j += 1;
        }

        let dist = hull[i].dist_sq(hull[j.min(n - 1)]);
        if dist > max_dist {
            max_dist = dist;
        }
    }

    max_dist.sqrt()
}

/// 凸包最小宽度（旋转卡壳）
///
/// # 算法
/// 计算凸包所有对边之间的最小距离
///
/// # 复杂度
/// - 时间: O(n)
/// - 空间: O(1)
pub fn rotating_calipers_width(hull: &[Point]) -> f64 {
    let n = hull.len();
    if n <= 2 {
        return 0.0;
    }

    let mut j = 1;
    let mut min_width = f64::MAX;

    for i in 0..n {
        let ni = (i + 1) % n;
        let edge = hull[ni].sub(hull[i]);

        // 找到距离边i最远的点
        while (hull[(j + 1) % n].sub(hull[i])).cross(edge).abs()
            > (hull[j].sub(hull[i])).cross(edge).abs()
        {
            j = (j + 1) % n;
        }

        // 计算点到直线的距离
        let line = Line::from_points(hull[i], hull[ni]);
        let width = line.distance_to(hull[j]);
        min_width = min_width.min(width);
    }

    min_width
}

/// 最小面积外接矩形（旋转卡壳）
///
/// # 返回值
/// (矩形中心, 宽度, 高度, 旋转角度)
///
/// # 复杂度
/// - 时间: O(n)
/// - 空间: O(1)
pub fn minimum_bounding_rectangle(hull: &[Point]) -> (Point, f64, f64, f64) {
    let n = hull.len();
    if n <= 1 {
        return (hull.get(0).copied().unwrap_or(Point::origin()), 0.0, 0.0, 0.0);
    }
    if n == 2 {
        let center = hull[0].add(hull[1]).mul(0.5);
        let w = hull[0].dist(hull[1]);
        return (center, w, 0.0, hull[1].sub(hull[0]).angle());
    }

    let mut min_area = f64::MAX;
    let mut result = (Point::origin(), 0.0, 0.0, 0.0);

    // 四条边的指针
    let mut i = 0;
    let mut j = 1;
    let mut k = 1;
    let mut l = 1;

    while i < n {
        let ni = (i + 1) % n;
        let edge_i = hull[ni].sub(hull[i]);
        let theta = edge_i.angle();

        // 更新j（与边i平行的最远点）
        while (hull[(j + 1) % n].sub(hull[i])).dot(edge_i)
            > (hull[j].sub(hull[i])).dot(edge_i)
        {
            j = (j + 1) % n;
        }

        // 更新k（与边i垂直的最远点）
        let perp = Point::new(-edge_i.y, edge_i.x);
        while (hull[(k + 1) % n].sub(hull[i])).dot(perp)
            > (hull[k].sub(hull[i])).dot(perp)
        {
            k = (k + 1) % n;
        }

        // 更新l（与j平行的边）
        if i == 0 {
            l = j;
        }
        let edge_l = hull[(l + 1) % n].sub(hull[l]);
        while edge_l.cross(edge_i) > 1e-9 {
            l = (l + 1) % n;
        }

        // 计算矩形尺寸
        let width = (hull[j].sub(hull[i])).dot(edge_i.normalize());
        let height = (hull[k].sub(hull[i])).dot(perp.normalize());
        let area = width * height;

        if area < min_area {
            min_area = area;
            // 计算中心点（简化处理）
            let center = hull[i].add(hull[j]).add(hull[k]).add(hull[l]).mul(0.25);
            result = (center, width, height, theta);
        }

        i += 1;
    }

    result
}

/// 最近点对（分治算法）
///
/// # 算法
/// 1. 按x坐标排序
/// 2. 递归求解左右两半的最近点对
/// 3. 检查跨越中线的点对
///
/// # 复杂度
/// - 时间: O(n log n)
/// - 空间: O(n)
pub fn closest_pair(points: &[Point]) -> f64 {
    let n = points.len();
    if n <= 1 {
        return f64::INFINITY;
    }

    let mut pts: Vec<Point> = points.to_vec();
    pts.sort_by(|a, b| a.x.partial_cmp(&b.x).unwrap());

    closest_pair_recursive(&pts)
}

fn closest_pair_recursive(pts: &[Point]) -> f64 {
    let n = pts.len();
    if n <= 3 {
        return closest_pair_brute_force(pts);
    }

    let mid = n / 2;
    let mid_point = pts[mid];

    let dl = closest_pair_recursive(&pts[..mid]);
    let dr = closest_pair_recursive(&pts[mid..]);
    let mut d = dl.min(dr);

    // 收集靠近分割线的点
    let mut strip: Vec<Point> = pts
        .iter()
        .filter(|p| (p.x - mid_point.x).abs() < d)
        .copied()
        .collect();

    // 按y排序
    strip.sort_by(|a, b| a.y.partial_cmp(&b.y).unwrap());

    // 检查strip中的点对
    for i in 0..strip.len() {
        for j in (i + 1)..strip.len().min(i + 7) {
            if strip[j].y - strip[i].y >= d {
                break;
            }
            d = d.min(strip[i].dist(strip[j]));
        }
    }

    d
}

fn closest_pair_brute_force(points: &[Point]) -> f64 {
    let n = points.len();
    let mut min_dist = f64::INFINITY;

    for i in 0..n {
        for j in (i + 1)..n {
            min_dist = min_dist.min(points[i].dist(points[j]));
        }
    }

    min_dist
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_point_operations() {
        let p1 = Point::new(1.0, 2.0);
        let p2 = Point::new(3.0, 4.0);

        let sum = p1.add(p2);
        assert_eq!(sum.x, 4.0);
        assert_eq!(sum.y, 6.0);

        let diff = p2.sub(p1);
        assert_eq!(diff.x, 2.0);
        assert_eq!(diff.y, 2.0);

        assert_eq!(p1.dot(p2), 11.0); // 1*3 + 2*4 = 11
        assert_eq!(p1.cross(p2), -2.0); // 1*4 - 2*3 = -2

        assert!((p1.len() - (5.0f64).sqrt()).abs() < 1e-9);
        assert!((p1.dist(p2) - 8.0f64.sqrt()).abs() < 1e-9);
    }

    #[test]
    fn test_point_rotate() {
        let p = Point::new(1.0, 0.0);
        let r90 = p.rotate(PI / 2.0);
        assert!((r90.x - 0.0).abs() < 1e-9);
        assert!((r90.y - 1.0).abs() < 1e-9);
    }

    #[test]
    fn test_segment_intersection() {
        let s1 = Segment::new(Point::new(0.0, 0.0), Point::new(2.0, 2.0));
        let s2 = Segment::new(Point::new(0.0, 2.0), Point::new(2.0, 0.0));
        assert!(s1.intersect(&s2));

        let pt = s1.intersection(&s2).unwrap();
        assert!((pt.x - 1.0).abs() < 1e-9);
        assert!((pt.y - 1.0).abs() < 1e-9);

        // 不相交
        let s3 = Segment::new(Point::new(3.0, 0.0), Point::new(3.0, 2.0));
        assert!(!s1.intersect(&s3));
    }

    #[test]
    fn test_circle() {
        let c = Circle::new(Point::new(0.0, 0.0), 5.0);
        
        assert_eq!(c.point_position(Point::new(3.0, 4.0)), 0); // 圆上
        assert_eq!(c.point_position(Point::new(1.0, 1.0)), -1); // 圆内
        assert_eq!(c.point_position(Point::new(5.0, 5.0)), 1); // 圆外

        // 两圆相交
        let c2 = Circle::new(Point::new(3.0, 4.0), 5.0);
        assert_eq!(c.relation(&c2), 2); // 相交
        
        let intersections = c.intersections(&c2);
        assert_eq!(intersections.len(), 2);
    }

    #[test]
    fn test_polygon_area() {
        // 正方形
        let square = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
        ]);
        assert!((square.area() - 1.0).abs() < 1e-9);

        // 三角形
        let triangle = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(0.0, 3.0),
        ]);
        assert!((triangle.area() - 3.0).abs() < 1e-9);
    }

    #[test]
    fn test_polygon_contains() {
        let square = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(2.0, 2.0),
            Point::new(0.0, 2.0),
        ]);

        assert!(square.contains(Point::new(1.0, 1.0))); // 内部
        assert!(square.contains(Point::new(0.0, 1.0))); // 边上
        assert!(!square.contains(Point::new(3.0, 1.0))); // 外部
    }

    #[test]
    fn test_convex_hull() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(0.5, 0.5),
            Point::new(0.0, 1.0),
            Point::new(1.0, 1.0),
        ];

        let hull = convex_hull(&points);
        assert_eq!(hull.len(), 4);
        
        // 验证凸包是凸的
        let hull_poly = Polygon::new(hull);
        assert!(hull_poly.is_convex());
    }

    #[test]
    fn test_convex_hull_collinear() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(2.0, 2.0),
            Point::new(3.0, 3.0),
        ];

        let hull = convex_hull(&points);
        assert_eq!(hull.len(), 2); // 只保留端点
    }

    #[test]
    fn test_rotating_calipers_diameter() {
        // 简单的两点情况
        let hull = vec![
            Point::new(0.0, 0.0),
            Point::new(3.0, 4.0),
        ];

        let diameter = rotating_calipers_diameter(&hull);
        // 两点距离 = 5
        assert!((diameter - 5.0).abs() < 1e-6, 
                "diameter = {} != 5.0", diameter);
    }

    #[test]
    fn test_closest_pair() {
        let points = vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(0.0, 2.0),
            Point::new(3.0, 3.0),
        ];

        let min_dist = closest_pair(&points);
        assert!((min_dist - 1.0).abs() < 1e-9); // (0,0) 和 (1,0) 距离为1
    }

    #[test]
    fn test_line() {
        let l = Line::from_points(Point::new(0.0, 0.0), Point::new(1.0, 1.0));
        
        assert!(l.contains(Point::new(2.0, 2.0)));
        assert!(!l.contains(Point::new(2.0, 3.0)));

        let dist = l.distance_to(Point::new(0.0, 1.0));
        assert!((dist - (2.0f64).sqrt() / 2.0).abs() < 1e-9);

        // 两直线交点
        let l2 = Line::from_points(Point::new(0.0, 1.0), Point::new(1.0, 0.0));
        let inter = l.intersection(&l2).unwrap();
        assert!((inter.x - 0.5).abs() < 1e-9);
        assert!((inter.y - 0.5).abs() < 1e-9);
    }

    #[test]
    fn test_polygon_perimeter() {
        let square = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(1.0, 0.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 1.0),
        ]);
        assert!((square.perimeter() - 4.0).abs() < 1e-9);
    }

    #[test]
    fn test_is_convex() {
        let convex = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(2.0, 2.0),
            Point::new(1.0, 1.0),
            Point::new(0.0, 2.0),
        ]);
        assert!(!convex.is_convex()); // 凹多边形

        let real_convex = Polygon::new(vec![
            Point::new(0.0, 0.0),
            Point::new(2.0, 0.0),
            Point::new(2.0, 2.0),
            Point::new(0.0, 2.0),
        ]);
        assert!(real_convex.is_convex());
    }
}

// 随机数支持（用于最小覆盖圆算法）
mod rand {
    use std::cell::Cell;
    
    thread_local! {
        static SEED: Cell<u64> = Cell::new(0x123456789abcdefu64);
    }
    
    pub fn random<T>() -> T
    where
        T: From<f64>,
    {
        SEED.with(|seed| {
            let s = seed.get();
            // xorshift
            let mut x = s;
            x ^= x << 13;
            x ^= x >> 7;
            x ^= x << 17;
            seed.set(x);
            T::from((x as f64) / (u64::MAX as f64))
        })
    }
}
