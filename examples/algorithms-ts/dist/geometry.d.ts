/**
 * 计算几何算法集合
 */
export type Point = {
    x: number;
    y: number;
};
/**
 * 叉积 (b - a) × (c - a)
 */
export declare function cross(a: Point, b: Point, c: Point): number;
/**
 * 点积
 */
export declare function dot(a: Point, b: Point, c: Point): number;
/**
 * 凸包（Graham Scan / Monotone Chain）
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
export declare function convexHull(points: Point[]): Point[];
/**
 * 最近点对（分治法）
 * 时间复杂度: O(n log n)
 */
export declare function closestPair(points: Point[]): number;
/**
 * 线段相交判断
 */
export declare function segmentsIntersect(p1: Point, p2: Point, p3: Point, p4: Point): boolean;
export declare function runGeometryTests(): void;
//# sourceMappingURL=geometry.d.ts.map