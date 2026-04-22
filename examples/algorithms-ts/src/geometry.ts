/**
 * 计算几何算法集合
 */

import { runTests, assertEq, assertTrue, assertArrayEq } from "./utils";

export type Point = { x: number; y: number };

/**
 * 叉积 (b - a) × (c - a)
 */
export function cross(a: Point, b: Point, c: Point): number {
  return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}

/**
 * 点积
 */
export function dot(a: Point, b: Point, c: Point): number {
  return (b.x - a.x) * (c.x - a.x) + (b.y - a.y) * (c.y - a.y);
}

/**
 * 凸包（Graham Scan / Monotone Chain）
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
export function convexHull(points: Point[]): Point[] {
  if (points.length <= 1) return points.slice();
  const pts = points.slice().sort((a, b) => a.x === b.x ? a.y - b.y : a.x - b.x);
  const lower: Point[] = [];
  for (const p of pts) {
    while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], p) <= 0) {
      lower.pop();
    }
    lower.push(p);
  }
  const upper: Point[] = [];
  for (let i = pts.length - 1; i >= 0; i--) {
    const p = pts[i];
    while (upper.length >= 2 && cross(upper[upper.length - 2], upper[upper.length - 1], p) <= 0) {
      upper.pop();
    }
    upper.push(p);
  }
  lower.pop();
  upper.pop();
  return lower.concat(upper);
}

/**
 * 最近点对（分治法）
 * 时间复杂度: O(n log n)
 */
export function closestPair(points: Point[]): number {
  if (points.length < 2) return Infinity;
  const px = points.slice().sort((a, b) => a.x - b.x);
  const py = points.slice().sort((a, b) => a.y - b.y);
  return _closestPair(px, py);
}

function dist(a: Point, b: Point): number {
  const dx = a.x - b.x, dy = a.y - b.y;
  return Math.sqrt(dx * dx + dy * dy);
}

function _closestPair(px: Point[], py: Point[]): number {
  const n = px.length;
  if (n <= 3) {
    let best = Infinity;
    for (let i = 0; i < n; i++) {
      for (let j = i + 1; j < n; j++) {
        best = Math.min(best, dist(px[i], px[j]));
      }
    }
    return best;
  }
  const mid = Math.floor(n / 2);
  const midPoint = px[mid];
  const pyl: Point[] = [], pyr: Point[] = [];
  for (const p of py) {
    if (p.x <= midPoint.x) pyl.push(p);
    else pyr.push(p);
  }
  const dl = _closestPair(px.slice(0, mid), pyl);
  const dr = _closestPair(px.slice(mid), pyr);
  let d = Math.min(dl, dr);
  const strip: Point[] = [];
  for (const p of py) {
    if (Math.abs(p.x - midPoint.x) < d) strip.push(p);
  }
  for (let i = 0; i < strip.length; i++) {
    for (let j = i + 1; j < strip.length && (strip[j].y - strip[i].y) < d; j++) {
      d = Math.min(d, dist(strip[i], strip[j]));
    }
  }
  return d;
}

/**
 * 线段相交判断
 */
export function segmentsIntersect(p1: Point, p2: Point, p3: Point, p4: Point): boolean {
  const d1 = cross(p3, p4, p1);
  const d2 = cross(p3, p4, p2);
  const d3 = cross(p1, p2, p3);
  const d4 = cross(p1, p2, p4);
  if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
      ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0))) return true;
  if (d1 === 0 && onSegment(p3, p4, p1)) return true;
  if (d2 === 0 && onSegment(p3, p4, p2)) return true;
  if (d3 === 0 && onSegment(p1, p2, p3)) return true;
  if (d4 === 0 && onSegment(p1, p2, p4)) return true;
  return false;
}

function onSegment(s: Point, e: Point, p: Point): boolean {
  return Math.min(s.x, e.x) <= p.x && p.x <= Math.max(s.x, e.x) &&
         Math.min(s.y, e.y) <= p.y && p.y <= Math.max(s.y, e.y);
}

export function runGeometryTests(): void {
  runTests("Geometry", {
    "convexHull": () => {
      const pts = [{ x: 0, y: 0 }, { x: 1, y: 1 }, { x: 1, y: 0 }, { x: 0, y: 1 }, { x: 0.5, y: 0.5 }];
      const hull = convexHull(pts);
      assertEq(hull.length, 4);
    },
    "closestPair": () => {
      const pts = [{ x: 2, y: 3 }, { x: 12, y: 30 }, { x: 40, y: 50 }, { x: 5, y: 1 }, { x: 12, y: 10 }];
      const d = closestPair(pts);
      assertTrue(Math.abs(d - Math.sqrt(13)) < 1e-6); // closest: (2,3)-(5,1)
    },
    "segmentsIntersect": () => {
      assertTrue(segmentsIntersect({ x: 0, y: 0 }, { x: 10, y: 10 }, { x: 0, y: 10 }, { x: 10, y: 0 }));
      assertTrue(!segmentsIntersect({ x: 0, y: 0 }, { x: 5, y: 5 }, { x: 6, y: 6 }, { x: 10, y: 10 }));
    },
  });
}
