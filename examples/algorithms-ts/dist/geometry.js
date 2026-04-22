"use strict";
/**
 * 计算几何算法集合
 */
Object.defineProperty(exports, "__esModule", { value: true });
exports.cross = cross;
exports.dot = dot;
exports.convexHull = convexHull;
exports.closestPair = closestPair;
exports.segmentsIntersect = segmentsIntersect;
exports.runGeometryTests = runGeometryTests;
const utils_1 = require("./utils");
/**
 * 叉积 (b - a) × (c - a)
 */
function cross(a, b, c) {
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}
/**
 * 点积
 */
function dot(a, b, c) {
    return (b.x - a.x) * (c.x - a.x) + (b.y - a.y) * (c.y - a.y);
}
/**
 * 凸包（Graham Scan / Monotone Chain）
 * 时间复杂度: O(n log n)
 * 空间复杂度: O(n)
 */
function convexHull(points) {
    if (points.length <= 1)
        return points.slice();
    const pts = points.slice().sort((a, b) => a.x === b.x ? a.y - b.y : a.x - b.x);
    const lower = [];
    for (const p of pts) {
        while (lower.length >= 2 && cross(lower[lower.length - 2], lower[lower.length - 1], p) <= 0) {
            lower.pop();
        }
        lower.push(p);
    }
    const upper = [];
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
function closestPair(points) {
    if (points.length < 2)
        return Infinity;
    const px = points.slice().sort((a, b) => a.x - b.x);
    const py = points.slice().sort((a, b) => a.y - b.y);
    return _closestPair(px, py);
}
function dist(a, b) {
    const dx = a.x - b.x, dy = a.y - b.y;
    return Math.sqrt(dx * dx + dy * dy);
}
function _closestPair(px, py) {
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
    const pyl = [], pyr = [];
    for (const p of py) {
        if (p.x <= midPoint.x)
            pyl.push(p);
        else
            pyr.push(p);
    }
    const dl = _closestPair(px.slice(0, mid), pyl);
    const dr = _closestPair(px.slice(mid), pyr);
    let d = Math.min(dl, dr);
    const strip = [];
    for (const p of py) {
        if (Math.abs(p.x - midPoint.x) < d)
            strip.push(p);
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
function segmentsIntersect(p1, p2, p3, p4) {
    const d1 = cross(p3, p4, p1);
    const d2 = cross(p3, p4, p2);
    const d3 = cross(p1, p2, p3);
    const d4 = cross(p1, p2, p4);
    if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) &&
        ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)))
        return true;
    if (d1 === 0 && onSegment(p3, p4, p1))
        return true;
    if (d2 === 0 && onSegment(p3, p4, p2))
        return true;
    if (d3 === 0 && onSegment(p1, p2, p3))
        return true;
    if (d4 === 0 && onSegment(p1, p2, p4))
        return true;
    return false;
}
function onSegment(s, e, p) {
    return Math.min(s.x, e.x) <= p.x && p.x <= Math.max(s.x, e.x) &&
        Math.min(s.y, e.y) <= p.y && p.y <= Math.max(s.y, e.y);
}
function runGeometryTests() {
    (0, utils_1.runTests)("Geometry", {
        "convexHull": () => {
            const pts = [{ x: 0, y: 0 }, { x: 1, y: 1 }, { x: 1, y: 0 }, { x: 0, y: 1 }, { x: 0.5, y: 0.5 }];
            const hull = convexHull(pts);
            (0, utils_1.assertEq)(hull.length, 4);
        },
        "closestPair": () => {
            const pts = [{ x: 2, y: 3 }, { x: 12, y: 30 }, { x: 40, y: 50 }, { x: 5, y: 1 }, { x: 12, y: 10 }];
            const d = closestPair(pts);
            (0, utils_1.assertTrue)(Math.abs(d - Math.sqrt(425)) < 1e-6);
        },
        "segmentsIntersect": () => {
            (0, utils_1.assertTrue)(segmentsIntersect({ x: 0, y: 0 }, { x: 10, y: 10 }, { x: 0, y: 10 }, { x: 10, y: 0 }));
            (0, utils_1.assertTrue)(!segmentsIntersect({ x: 0, y: 0 }, { x: 5, y: 5 }, { x: 6, y: 6 }, { x: 10, y: 10 }));
        },
    });
}
//# sourceMappingURL=geometry.js.map