// LeetCode 223. Rectangle Area
// https://leetcode.com/problems/rectangle-area/
//
// Problem: Given the coordinates of two rectilinear rectangles in a 2D plane,
// return the total area covered by the two rectangles.
//
// Formal specification:
// - Pre: rectangles are axis-aligned, x1 < x2 and y1 < y2 for each
// - Post: area of the union of the two rectangles
//
// Algorithm: Inclusion-exclusion principle.
//   total = area(A) + area(B) - overlap(A, B)
//   overlap exists iff max(x1) < min(x2) and max(y1) < min(y2)
// Time: O(1), Space: O(1).

package leetcode

// ComputeArea 计算两个轴对齐矩形覆盖的总面积。
// 使用容斥原理：总面积 = areaA + areaB - overlap。
func ComputeArea(ax1, ay1, ax2, ay2, bx1, by1, bx2, by2 int) int {
	areaA := (ax2 - ax1) * (ay2 - ay1)
	areaB := (bx2 - bx1) * (by2 - by1)

	left := rectMax(ax1, bx1)
	right := rectMin(ax2, bx2)
	bottom := rectMax(ay1, by1)
	top := rectMin(ay2, by2)

	overlap := 0
	if left < right && bottom < top {
		overlap = (right - left) * (top - bottom)
	}

	return areaA + areaB - overlap
}

func rectMax(a, b int) int {
	if a > b {
		return a
	}
	return b
}

func rectMin(a, b int) int {
	if a < b {
		return a
	}
	return b
}
