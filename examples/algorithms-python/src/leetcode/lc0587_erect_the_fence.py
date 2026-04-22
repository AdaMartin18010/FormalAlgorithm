"""
LeetCode 587. 安装栅栏

给定若干棵树的坐标，返回能够包含所有这些树的最小面积凸多边形（凸包）的顶点坐标，
要求所有在边界上的树都包含在结果中。

思路：Andrew 单调链（Monotone Chain）求凸包
1. 将所有点按 x 升序、x 相同按 y 升序排序。
2. 构造下凸壳（从左到右）：维护栈，若新点使最后三点形成顺时针转向（叉积 < 0），
   则弹出栈顶，直到形成逆时针或共线。
3. 构造上凸壳（从右到左），同理。
4. 合并下凸壳和上凸壳，去除重复端点。

叉积 cross(O, A, B) = (A.x - O.x)*(B.y - O.y) - (A.y - O.y)*(B.x - O.x)
- cross > 0：逆时针（左转）
- cross < 0：顺时针（右转）
- cross = 0：共线

使用 cross < 0 作为弹出条件，可保留所有共线的边界点。

时间复杂度：O(n log n)，空间复杂度：O(n)。
"""

from typing import List


def _cross(o: List[int], a: List[int], b: List[int]) -> int:
    """计算二维向量 OA × OB 的叉积。"""
    return (a[0] - o[0]) * (b[1] - o[1]) - (a[1] - o[1]) * (b[0] - o[0])


def outer_trees(points: List[List[int]]) -> List[List[int]]:
    """返回包围所有点的凸包坐标，包含边界上的所有点。"""
    n = len(points)
    if n <= 3:
        return points

    # 按 x 升序，x 相同按 y 升序排序
    points = sorted(points, key=lambda p: (p[0], p[1]))

    # 构造下凸壳
    lower: List[List[int]] = []
    for p in points:
        while len(lower) >= 2 and _cross(lower[-2], lower[-1], p) < 0:
            lower.pop()
        lower.append(p)

    # 构造上凸壳
    upper: List[List[int]] = []
    for p in reversed(points):
        while len(upper) >= 2 and _cross(upper[-2], upper[-1], p) < 0:
            upper.pop()
        upper.append(p)

    # 合并并去重（保持顺序）
    seen = set()
    result: List[List[int]] = []
    for p in lower + upper:
        key = (p[0], p[1])
        if key not in seen:
            seen.add(key)
            result.append(p)

    return result


# --- Tests ---
if __name__ == "__main__":
    # 示例 1
    pts1 = [[1, 1], [2, 2], [2, 0], [2, 4], [3, 3], [4, 2]]
    assert sorted(outer_trees(pts1)) == sorted([[1, 1], [2, 0], [2, 4], [3, 3], [4, 2]])

    # 示例 2（共线）
    pts2 = [[1, 2], [2, 2], [4, 2]]
    assert sorted(outer_trees(pts2)) == sorted([[1, 2], [2, 2], [4, 2]])

    # 矩形含共线边界点
    pts3 = [[1, 1], [1, 3], [2, 1], [2, 3], [3, 1], [3, 3]]
    assert sorted(outer_trees(pts3)) == sorted(
        [[1, 1], [1, 3], [2, 1], [2, 3], [3, 1], [3, 3]]
    )

    # 单点
    assert outer_trees([[0, 0]]) == [[0, 0]]

    # 两点
    assert sorted(outer_trees([[0, 0], [1, 1]])) == sorted([[0, 0], [1, 1]])

    print("All tests passed for LC 587 - Erect the Fence")
