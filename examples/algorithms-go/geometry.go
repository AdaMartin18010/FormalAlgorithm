// Package algorithms provides computational geometry implementations in Go.
package algorithms

import (
	"math"
	"sort"
)

// Point represents a 2D point.
type Point struct {
	X, Y float64
}

// cross returns the cross product (b-a) x (c-a).
func cross(a, b, c Point) float64 {
	return (b.X-a.X)*(c.Y-a.Y) - (b.Y-a.Y)*(c.X-a.X)
}

// ConvexHull computes the convex hull using Monotone Chain.
// Time complexity: O(n log n)
func ConvexHull(points []Point) []Point {
	n := len(points)
	if n <= 1 {
		return append([]Point{}, points...)
	}
	pts := make([]Point, n)
	copy(pts, points)
	sort.Slice(pts, func(i, j int) bool {
		if pts[i].X == pts[j].X {
			return pts[i].Y < pts[j].Y
		}
		return pts[i].X < pts[j].X
	})
	lower := make([]Point, 0, n)
	for _, p := range pts {
		for len(lower) >= 2 && cross(lower[len(lower)-2], lower[len(lower)-1], p) <= 0 {
			lower = lower[:len(lower)-1]
		}
		lower = append(lower, p)
	}
	upper := make([]Point, 0, n)
	for i := n - 1; i >= 0; i-- {
		p := pts[i]
		for len(upper) >= 2 && cross(upper[len(upper)-2], upper[len(upper)-1], p) <= 0 {
			upper = upper[:len(upper)-1]
		}
		upper = append(upper, p)
	}
	lower = lower[:len(lower)-1]
	upper = upper[:len(upper)-1]
	return append(lower, upper...)
}

// dist returns Euclidean distance between two points.
func dist(a, b Point) float64 {
	dx := a.X - b.X
	dy := a.Y - b.Y
	return math.Sqrt(dx*dx + dy*dy)
}

// ClosestPair finds the closest pair of points.
// Time complexity: O(n log n)
func ClosestPair(points []Point) float64 {
	if len(points) < 2 {
		return math.Inf(1)
	}
	px := make([]Point, len(points))
	py := make([]Point, len(points))
	copy(px, points)
	copy(py, points)
	sort.Slice(px, func(i, j int) bool { return px[i].X < px[j].X })
	sort.Slice(py, func(i, j int) bool { return py[i].Y < py[j].Y })
	return closestPairRec(px, py, 0, len(px))
}

func closestPairRec(px, py []Point, l, r int) float64 {
	n := r - l
	if n <= 3 {
		best := math.Inf(1)
		for i := l; i < r; i++ {
			for j := i + 1; j < r; j++ {
				if d := dist(px[i], px[j]); d < best {
					best = d
				}
			}
		}
		return best
	}
	mid := l + n/2
	midPoint := px[mid]
	pyl := make([]Point, 0, mid-l)
	pyr := make([]Point, 0, r-mid)
	for _, p := range py {
		if p.X <= midPoint.X {
			pyl = append(pyl, p)
		} else {
			pyr = append(pyr, p)
		}
	}
	dl := closestPairRec(px, pyl, l, mid)
	dr := closestPairRec(px, pyr, mid, r)
	d := dl
	if dr < d {
		d = dr
	}
	strip := make([]Point, 0)
	for _, p := range py {
		if math.Abs(p.X-midPoint.X) < d {
			strip = append(strip, p)
		}
	}
	for i := 0; i < len(strip); i++ {
		for j := i + 1; j < len(strip) && (strip[j].Y-strip[i].Y) < d; j++ {
			if di := dist(strip[i], strip[j]); di < d {
				d = di
			}
		}
	}
	return d
}

// SegmentsIntersect checks if two line segments intersect.
func SegmentsIntersect(p1, p2, p3, p4 Point) bool {
	d1 := cross(p3, p4, p1)
	d2 := cross(p3, p4, p2)
	d3 := cross(p1, p2, p3)
	d4 := cross(p1, p2, p4)
	if ((d1 > 0 && d2 < 0) || (d1 < 0 && d2 > 0)) && ((d3 > 0 && d4 < 0) || (d3 < 0 && d4 > 0)) {
		return true
	}
	if d1 == 0 && onSegment(p3, p4, p1) { return true }
	if d2 == 0 && onSegment(p3, p4, p2) { return true }
	if d3 == 0 && onSegment(p1, p2, p3) { return true }
	if d4 == 0 && onSegment(p1, p2, p4) { return true }
	return false
}

func onSegment(s, e, p Point) bool {
	return math.Min(s.X, e.X) <= p.X && p.X <= math.Max(s.X, e.X) &&
		math.Min(s.Y, e.Y) <= p.Y && p.Y <= math.Max(s.Y, e.Y)
}
