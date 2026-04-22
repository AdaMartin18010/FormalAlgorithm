/**
 * geometry.cpp - C++计算几何算法实现
 * 包含: 凸包、最近点对、线段相交
 */

#include <vector>
#include <algorithm>
#include <cmath>

namespace geometry {

struct Point {
    double x, y;
    bool operator<(const Point& other) const {
        return x < other.x || (x == other.x && y < other.y);
    }
};

/**
 * 叉积 (b-a) x (c-a)
 */
double cross(const Point& a, const Point& b, const Point& c) {
    return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
}

/**
 * 凸包 (Monotone Chain)
 * 时间复杂度: O(n log n)
 */
std::vector<Point> convexHull(std::vector<Point> points) {
    int n = points.size();
    if (n <= 1) return points;
    std::sort(points.begin(), points.end());
    std::vector<Point> lower, upper;
    for (const auto& p : points) {
        while (lower.size() >= 2 && cross(lower[lower.size()-2], lower.back(), p) <= 0)
            lower.pop_back();
        lower.push_back(p);
    }
    for (int i = n - 1; i >= 0; i--) {
        const auto& p = points[i];
        while (upper.size() >= 2 && cross(upper[upper.size()-2], upper.back(), p) <= 0)
            upper.pop_back();
        upper.push_back(p);
    }
    lower.pop_back();
    upper.pop_back();
    lower.insert(lower.end(), upper.begin(), upper.end());
    return lower;
}

double dist(const Point& a, const Point& b) {
    double dx = a.x - b.x, dy = a.y - b.y;
    return std::sqrt(dx*dx + dy*dy);
}

double closestPairRec(std::vector<Point>& px, std::vector<Point>& py, int l, int r) {
    int n = r - l;
    if (n <= 3) {
        double best = 1e18;
        for (int i = l; i < r; i++)
            for (int j = i + 1; j < r; j++)
                best = std::min(best, dist(px[i], px[j]));
        return best;
    }
    int mid = l + n / 2;
    auto midPoint = px[mid];
    std::vector<Point> pyl, pyr;
    for (const auto& p : py) {
        if (p.x <= midPoint.x) pyl.push_back(p); else pyr.push_back(p);
    }
    double dl = closestPairRec(px, pyl, l, mid);
    double dr = closestPairRec(px, pyr, mid, r);
    double d = std::min(dl, dr);
    std::vector<Point> strip;
    for (const auto& p : py) if (std::abs(p.x - midPoint.x) < d) strip.push_back(p);
    for (size_t i = 0; i < strip.size(); i++)
        for (size_t j = i + 1; j < strip.size() && (strip[j].y - strip[i].y) < d; j++)
            d = std::min(d, dist(strip[i], strip[j]));
    return d;
}

/**
 * 最近点对
 * 时间复杂度: O(n log n)
 */
double closestPair(std::vector<Point> points) {
    if (points.size() < 2) return 1e18;
    auto px = points;
    auto py = points;
    std::sort(px.begin(), px.end(), [](const Point& a, const Point& b) { return a.x < b.x; });
    std::sort(py.begin(), py.end(), [](const Point& a, const Point& b) { return a.y < b.y; });
    return closestPairRec(px, py, 0, px.size());
}

bool onSegment(const Point& s, const Point& e, const Point& p) {
    return std::min(s.x, e.x) <= p.x && p.x <= std::max(s.x, e.x)
        && std::min(s.y, e.y) <= p.y && p.y <= std::max(s.y, e.y);
}

/**
 * 线段相交判断
 */
bool segmentsIntersect(const Point& p1, const Point& p2, const Point& p3, const Point& p4) {
    double d1 = cross(p3, p4, p1);
    double d2 = cross(p3, p4, p2);
    double d3 = cross(p1, p2, p3);
    double d4 = cross(p1, p2, p4);
    if (((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0))) return true;
    if (d1 == 0 && onSegment(p3, p4, p1)) return true;
    if (d2 == 0 && onSegment(p3, p4, p2)) return true;
    if (d3 == 0 && onSegment(p1, p2, p3)) return true;
    if (d4 == 0 && onSegment(p1, p2, p4)) return true;
    return false;
}

} // namespace geometry
