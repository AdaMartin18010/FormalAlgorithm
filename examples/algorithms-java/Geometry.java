/**
 * 计算几何算法实现
 * 包含: 凸包、最近点对、线段相交
 */
public class Geometry {

    public static class Point {
        public double x, y;
        public Point(double x, double y) { this.x = x; this.y = y; }
    }

    /**
     * 叉积 (b-a) x (c-a)
     */
    public static double cross(Point a, Point b, Point c) {
        return (b.x - a.x) * (c.y - a.y) - (b.y - a.y) * (c.x - a.x);
    }

    /**
     * 凸包 (Monotone Chain)
     * 时间复杂度: O(n log n)
     */
    public static java.util.List<Point> convexHull(java.util.List<Point> points) {
        int n = points.size();
        if (n <= 1) return new java.util.ArrayList<>(points);
        Point[] pts = points.toArray(new Point[0]);
        java.util.Arrays.sort(pts, (a, b) -> {
            if (a.x != b.x) return Double.compare(a.x, b.x);
            return Double.compare(a.y, b.y);
        });
        java.util.List<Point> lower = new java.util.ArrayList<>();
        for (Point p : pts) {
            while (lower.size() >= 2 && cross(lower.get(lower.size()-2), lower.get(lower.size()-1), p) <= 0)
                lower.remove(lower.size()-1);
            lower.add(p);
        }
        java.util.List<Point> upper = new java.util.ArrayList<>();
        for (int i = pts.length - 1; i >= 0; i--) {
            Point p = pts[i];
            while (upper.size() >= 2 && cross(upper.get(upper.size()-2), upper.get(upper.size()-1), p) <= 0)
                upper.remove(upper.size()-1);
            upper.add(p);
        }
        lower.remove(lower.size()-1);
        upper.remove(upper.size()-1);
        lower.addAll(upper);
        return lower;
    }

    /**
     * 欧几里得距离
     */
    public static double dist(Point a, Point b) {
        double dx = a.x - b.x, dy = a.y - b.y;
        return Math.sqrt(dx*dx + dy*dy);
    }

    /**
     * 最近点对 (分治法)
     * 时间复杂度: O(n log n)
     */
    public static double closestPair(java.util.List<Point> points) {
        if (points.size() < 2) return Double.POSITIVE_INFINITY;
        Point[] px = points.toArray(new Point[0]);
        Point[] py = points.toArray(new Point[0]);
        java.util.Arrays.sort(px, (a, b) -> Double.compare(a.x, b.x));
        java.util.Arrays.sort(py, (a, b) -> Double.compare(a.y, b.y));
        return closestPairRec(px, py, 0, px.length);
    }

    private static double closestPairRec(Point[] px, Point[] py, int l, int r) {
        int n = r - l;
        if (n <= 3) {
            double best = Double.POSITIVE_INFINITY;
            for (int i = l; i < r; i++)
                for (int j = i+1; j < r; j++)
                    best = Math.min(best, dist(px[i], px[j]));
            return best;
        }
        int mid = l + n/2;
        Point midPoint = px[mid];
        java.util.List<Point> pyl = new java.util.ArrayList<>();
        java.util.List<Point> pyr = new java.util.ArrayList<>();
        for (Point p : py) {
            if (p.x <= midPoint.x) pyl.add(p); else pyr.add(p);
        }
        double dl = closestPairRec(px, pyl.toArray(new Point[0]), l, mid);
        double dr = closestPairRec(px, pyr.toArray(new Point[0]), mid, r);
        double d = Math.min(dl, dr);
        java.util.List<Point> strip = new java.util.ArrayList<>();
        for (Point p : py) if (Math.abs(p.x - midPoint.x) < d) strip.add(p);
        Point[] stripArr = strip.toArray(new Point[0]);
        for (int i = 0; i < stripArr.length; i++)
            for (int j = i+1; j < stripArr.length && (stripArr[j].y - stripArr[i].y) < d; j++)
                d = Math.min(d, dist(stripArr[i], stripArr[j]));
        return d;
    }

    /**
     * 线段相交判断
     */
    public static boolean segmentsIntersect(Point p1, Point p2, Point p3, Point p4) {
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

    private static boolean onSegment(Point s, Point e, Point p) {
        return Math.min(s.x, e.x) <= p.x && p.x <= Math.max(s.x, e.x)
            && Math.min(s.y, e.y) <= p.y && p.y <= Math.max(s.y, e.y);
    }
}
