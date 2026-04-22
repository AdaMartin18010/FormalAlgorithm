//! LeetCode 587. 安装栅栏
//!
//! 给定一个数组 `trees` 表示若干棵树的坐标，用一个整数数组 `[xi, yi]` 表示。
//! 你需要安装一个栅栏，使得所有树都在栅栏内部或边界上，并且所有在边界上的树都包含在结果中。
//! 返回能够包含所有这些树的最小面积凸多边形（凸包）的顶点坐标。
//!
//! # 核心思路
//!
//! **Andrew 单调链（Monotone Chain）** 求凸包：
//! 1. 将所有点按 x 坐标升序排序，x 相同则按 y 升序排序。
//! 2. 构造下凸壳（从左到右遍历）：维护一个栈，若新点使最后三点形成顺时针转向
//!   （叉积 < 0），则弹出栈顶，直到形成逆时针或共线。
//! 3. 构造上凸壳（从右到左遍历），同理。
//! 4. 将下凸壳和上凸壳合并，并去除重复端点。
//!
//! 叉积公式：`cross(O, A, B) = (A.x - O.x)*(B.y - O.y) - (A.y - O.y)*(B.x - O.x)`。
//! - cross > 0：逆时针（左转）
//! - cross < 0：顺时针（右转）
//! - cross = 0：共线
//!
//! 使用 cross < 0 作为弹出条件，可保留所有共线的边界点。
//!
//! # 复杂度分析
//!
//! - **时间复杂度**：O(n log n) — 主要开销在排序。
//! - **空间复杂度**：O(n) — 存储凸包点集。

/// 计算二维向量叉积（OA × OB）。
fn cross(o: &[i32], a: &[i32], b: &[i32]) -> i32 {
    (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])
}

/// 返回包围所有点的凸包坐标，包含边界上的所有点。
pub fn outer_trees(points: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
    let n = points.len();
    if n <= 3 {
        return points;
    }

    // 按 x 升序，x 相同按 y 升序排序
    let mut sorted = points;
    sorted.sort_by(|a, b| a[0].cmp(&b[0]).then_with(|| a[1].cmp(&b[1])));

    // 构造下凸壳（从左到右）
    let mut lower: Vec<Vec<i32>> = Vec::new();
    for p in &sorted {
        while lower.len() >= 2 && cross(&lower[lower.len() - 2], &lower[lower.len() - 1], p) < 0 {
            lower.pop();
        }
        lower.push(p.clone());
    }

    // 构造上凸壳（从右到左）
    let mut upper: Vec<Vec<i32>> = Vec::new();
    for p in sorted.iter().rev() {
        while upper.len() >= 2 && cross(&upper[upper.len() - 2], &upper[upper.len() - 1], p) < 0 {
            upper.pop();
        }
        upper.push(p.clone());
    }

    // 合并并去重（保持顺序）
    let mut result: Vec<Vec<i32>> = Vec::new();
    let mut seen = std::collections::HashSet::new();
    for p in lower.into_iter().chain(upper.into_iter()) {
        let key = (p[0], p[1]);
        if seen.insert(key) {
            result.push(p);
        }
    }

    result
}

#[cfg(test)]
mod tests {
    use super::*;

    fn sort_points(mut pts: Vec<Vec<i32>>) -> Vec<Vec<i32>> {
        pts.sort_by(|a, b| a[0].cmp(&b[0]).then_with(|| a[1].cmp(&b[1])));
        pts
    }

    #[test]
    fn test_example_1() {
        let points = vec![
            vec![1, 1],
            vec![2, 2],
            vec![2, 0],
            vec![2, 4],
            vec![3, 3],
            vec![4, 2],
        ];
        let result = sort_points(outer_trees(points));
        assert_eq!(
            result,
            vec![
                vec![1, 1],
                vec![2, 0],
                vec![2, 4],
                vec![3, 3],
                vec![4, 2],
            ]
        );
    }

    #[test]
    fn test_example_2() {
        let points = vec![vec![1, 2], vec![2, 2], vec![4, 2]];
        let result = sort_points(outer_trees(points));
        assert_eq!(result, vec![vec![1, 2], vec![2, 2], vec![4, 2]]);
    }

    #[test]
    fn test_rectangle_with_collinear() {
        let points = vec![
            vec![1, 1],
            vec![1, 3],
            vec![2, 1],
            vec![2, 3],
            vec![3, 1],
            vec![3, 3],
        ];
        let result = sort_points(outer_trees(points));
        assert_eq!(
            result,
            vec![
                vec![1, 1],
                vec![1, 3],
                vec![2, 1],
                vec![2, 3],
                vec![3, 1],
                vec![3, 3],
            ]
        );
    }

    #[test]
    fn test_single_point() {
        assert_eq!(outer_trees(vec![vec![0, 0]]), vec![vec![0, 0]]);
    }

    #[test]
    fn test_two_points() {
        let points = vec![vec![0, 0], vec![1, 1]];
        let result = sort_points(outer_trees(points));
        assert_eq!(result, vec![vec![0, 0], vec![1, 1]]);
    }
}
