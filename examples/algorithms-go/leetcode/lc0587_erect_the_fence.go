package leetcode

// LeetCode 587. 安装栅栏
//
// 给定若干棵树的坐标，返回能够包含所有这些树的最小面积凸多边形（凸包）的顶点坐标，
// 要求所有在边界上的树都包含在结果中。
//
// 思路：Andrew 单调链（Monotone Chain）求凸包
// 1. 将所有点按 x 升序、x 相同按 y 升序排序。
// 2. 构造下凸壳（从左到右）：维护栈，若新点使最后三点形成顺时针转向（叉积 < 0），
//    则弹出栈顶，直到形成逆时针或共线。
// 3. 构造上凸壳（从右到左），同理。
// 4. 合并下凸壳和上凸壳，去除重复端点。
//
// 叉积 cross(O, A, B) = (A.x - O.x)*(B.y - O.y) - (A.y - O.y)*(B.x - O.x)
// - cross > 0：逆时针（左转）
// - cross < 0：顺时针（右转）
// - cross = 0：共线
//
// 使用 cross < 0 作为弹出条件，可保留所有共线的边界点。
// 时间复杂度：O(n log n)，空间复杂度：O(n)。

// cross 计算二维向量 OA × OB 的叉积。
func cross(o, a, b []int) int {
	return (a[0]-o[0])*(b[1]-o[1]) - (a[1]-o[1])*(b[0]-o[0])
}

// OuterTrees 返回包围所有点的凸包坐标，包含边界上的所有点。
func OuterTrees(points [][]int) [][]int {
	n := len(points)
	if n <= 3 {
		return points
	}

	// 按 x 升序，x 相同按 y 升序排序
	sorted := make([][]int, n)
	copy(sorted, points)
	for i := range sorted {
		sorted[i] = make([]int, 2)
		copy(sorted[i], points[i])
	}
	for i := 0; i < n; i++ {
		for j := i + 1; j < n; j++ {
			if sorted[i][0] > sorted[j][0] || (sorted[i][0] == sorted[j][0] && sorted[i][1] > sorted[j][1]) {
				sorted[i], sorted[j] = sorted[j], sorted[i]
			}
		}
	}

	// 构造下凸壳（从左到右）
	lower := make([][]int, 0)
	for _, p := range sorted {
		for len(lower) >= 2 && cross(lower[len(lower)-2], lower[len(lower)-1], p) < 0 {
			lower = lower[:len(lower)-1]
		}
		lower = append(lower, p)
	}

	// 构造上凸壳（从右到左）
	upper := make([][]int, 0)
	for i := n - 1; i >= 0; i-- {
		p := sorted[i]
		for len(upper) >= 2 && cross(upper[len(upper)-2], upper[len(upper)-1], p) < 0 {
			upper = upper[:len(upper)-1]
		}
		upper = append(upper, p)
	}

	// 合并并去重（保持顺序）
	result := make([][]int, 0)
	seen := make(map[[2]int]bool)
	for _, p := range lower {
		key := [2]int{p[0], p[1]}
		if !seen[key] {
			seen[key] = true
			result = append(result, p)
		}
	}
	for _, p := range upper {
		key := [2]int{p[0], p[1]}
		if !seen[key] {
			seen[key] = true
			result = append(result, p)
		}
	}

	return result
}
