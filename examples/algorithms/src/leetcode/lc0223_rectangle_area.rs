//! LeetCode 223. 矩形面积
//!
//! 给你 二维 平面上两个 由直线构成且边与坐标轴平行 的矩形，
//! 请你计算并返回两个矩形覆盖的总面积。
//! 每个矩形由其 左下 顶点和 右上 顶点坐标表示。
//!
//! 对标: LeetCode 223

/// 计算两个轴对齐矩形覆盖的总面积。
///
/// # 形式化规约
///
/// - **前置条件 (Pre)**：对于每个矩形，左下角 x 坐标 < 右上角 x 坐标，左下角 y 坐标 < 右上角 y 坐标。
/// - **后置条件 (Post)**：返回两个矩形并集的面积，即 `area(A) + area(B) - area(A ∩ B)`。
///
/// # 核心思路
///
/// 容斥原理：总面积 = 矩形A面积 + 矩形B面积 - 重叠面积。
///
/// 重叠区域（若存在）也是轴对齐矩形，其边界为：
/// - 左边界：`max(ax1, bx1)`
/// - 右边界：`min(ax2, bx2)`
/// - 下边界：`max(ay1, by1)`
/// - 上边界：`min(ay2, by2)`
///
/// 当且仅当 `max(ax1, bx1) < min(ax2, bx2)` 且 `max(ay1, by1) < min(ay2, by2)` 时存在重叠。
/// 重叠面积为 `(right - left) * (top - bottom)`。
///
/// # 复杂度分析
///
/// - **时间复杂度**：O(1) — 仅涉及常数次算术运算和比较。
/// - **空间复杂度**：O(1) — 仅使用常数额外变量。
///
/// # 证明要点
///
/// - 两矩形并集面积由容斥原理给出：`|A ∪ B| = |A| + |B| - |A ∩ B|`。
/// - 交集存在当且仅当在 x 轴和 y 轴上的投影均相交。
/// - 投影相交条件：左边界 < 右边界 且 下边界 < 上边界。
pub fn compute_area(
    ax1: i32,
    ay1: i32,
    ax2: i32,
    ay2: i32,
    bx1: i32,
    by1: i32,
    bx2: i32,
    by2: i32,
) -> i32 {
    let area_a = (ax2 as i64 - ax1 as i64) * (ay2 as i64 - ay1 as i64);
    let area_b = (bx2 as i64 - bx1 as i64) * (by2 as i64 - by1 as i64);

    let left = std::cmp::max(ax1, bx1);
    let right = std::cmp::min(ax2, bx2);
    let bottom = std::cmp::max(ay1, by1);
    let top = std::cmp::min(ay2, by2);

    let overlap = if left < right && bottom < top {
        (right as i64 - left as i64) * (top as i64 - bottom as i64)
    } else {
        0
    };

    (area_a + area_b - overlap) as i32
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_example_1() {
        // 矩形A: (-3,0)到(3,4), 矩形B: (0,-1)到(9,2)
        assert_eq!(compute_area(-3, 0, 3, 4, 0, -1, 9, 2), 45);
    }

    #[test]
    fn test_example_2() {
        // 无重叠
        assert_eq!(compute_area(-2, -2, 2, 2, -4, -4, -3, -3), 17);
    }

    #[test]
    fn test_overlap_partial() {
        // 部分重叠
        assert_eq!(compute_area(0, 0, 2, 2, 1, 1, 3, 3), 7);
    }

    #[test]
    fn test_one_inside_other() {
        // 一个矩形完全包含另一个
        assert_eq!(compute_area(0, 0, 4, 4, 1, 1, 2, 2), 16);
    }

    #[test]
    fn test_edge_touching() {
        // 边相接（无重叠）
        assert_eq!(compute_area(0, 0, 2, 2, 2, 0, 4, 2), 8);
    }

    #[test]
    fn test_corner_touching() {
        // 角相接（无重叠）
        assert_eq!(compute_area(0, 0, 1, 1, 1, 1, 2, 2), 2);
    }

    #[test]
    fn test_large_values() {
        // 大数值测试，验证 i64 中间计算避免溢出
        assert_eq!(
            compute_area(-10_000, -10_000, 10_000, 10_000, -10_000, -10_000, 10_000, 10_000),
            400_000_000
        );
    }
}
