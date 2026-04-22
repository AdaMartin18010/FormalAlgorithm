package leetcode

import (
	"sort"
	"testing"
)

func sortPoints(pts [][]int) [][]int {
	sort.Slice(pts, func(i, j int) bool {
		if pts[i][0] != pts[j][0] {
			return pts[i][0] < pts[j][0]
		}
		return pts[i][1] < pts[j][1]
	})
	return pts
}

func pointsEqual(a, b [][]int) bool {
	if len(a) != len(b) {
		return false
	}
	a = sortPoints(a)
	b = sortPoints(b)
	for i := range a {
		if a[i][0] != b[i][0] || a[i][1] != b[i][1] {
			return false
		}
	}
	return true
}

func TestOuterTreesExample1(t *testing.T) {
	pts := [][]int{{1, 1}, {2, 2}, {2, 0}, {2, 4}, {3, 3}, {4, 2}}
	expected := [][]int{{1, 1}, {2, 0}, {2, 4}, {3, 3}, {4, 2}}
	result := OuterTrees(pts)
	if !pointsEqual(result, expected) {
		t.Errorf("OuterTrees example1) = %v, want %v", result, expected)
	}
}

func TestOuterTreesExample2(t *testing.T) {
	pts := [][]int{{1, 2}, {2, 2}, {4, 2}}
	expected := [][]int{{1, 2}, {2, 2}, {4, 2}}
	result := OuterTrees(pts)
	if !pointsEqual(result, expected) {
		t.Errorf("OuterTrees example2) = %v, want %v", result, expected)
	}
}

func TestOuterTreesRectangleWithCollinear(t *testing.T) {
	pts := [][]int{{1, 1}, {1, 3}, {2, 1}, {2, 3}, {3, 1}, {3, 3}}
	expected := [][]int{{1, 1}, {1, 3}, {2, 1}, {2, 3}, {3, 1}, {3, 3}}
	result := OuterTrees(pts)
	if !pointsEqual(result, expected) {
		t.Errorf("OuterTrees rectangle) = %v, want %v", result, expected)
	}
}

func TestOuterTreesSinglePoint(t *testing.T) {
	pts := [][]int{{0, 0}}
	result := OuterTrees(pts)
	if len(result) != 1 || result[0][0] != 0 || result[0][1] != 0 {
		t.Errorf("OuterTrees single) = %v, want [[0 0]]", result)
	}
}

func TestOuterTreesTwoPoints(t *testing.T) {
	pts := [][]int{{0, 0}, {1, 1}}
	expected := [][]int{{0, 0}, {1, 1}}
	result := OuterTrees(pts)
	if !pointsEqual(result, expected) {
		t.Errorf("OuterTrees two) = %v, want %v", result, expected)
	}
}
