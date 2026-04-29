package leetcode

import "testing"

func TestUniquePaths(t *testing.T) {
	// 示例 1
	if UniquePaths(3, 7) != 28 {
		t.Errorf("UniquePaths(3,7) = %d, want 28", UniquePaths(3, 7))
	}

	// 示例 2
	if UniquePaths(3, 2) != 3 {
		t.Errorf("UniquePaths(3,2) = %d, want 3", UniquePaths(3, 2))
	}

	// 示例 3
	if UniquePaths(7, 3) != 28 {
		t.Errorf("UniquePaths(7,3) = %d, want 28", UniquePaths(7, 3))
	}

	// 示例 4
	if UniquePaths(3, 3) != 6 {
		t.Errorf("UniquePaths(3,3) = %d, want 6", UniquePaths(3, 3))
	}

	// 边界：1x1
	if UniquePaths(1, 1) != 1 {
		t.Errorf("UniquePaths(1,1) = %d, want 1", UniquePaths(1, 1))
	}

	// 边界：1xn
	if UniquePaths(1, 100) != 1 {
		t.Errorf("UniquePaths(1,100) = %d, want 1", UniquePaths(1, 100))
	}

	// 边界：mx1
	if UniquePaths(100, 1) != 1 {
		t.Errorf("UniquePaths(100,1) = %d, want 1", UniquePaths(100, 1))
	}

	// 边界：2x2
	if UniquePaths(2, 2) != 2 {
		t.Errorf("UniquePaths(2,2) = %d, want 2", UniquePaths(2, 2))
	}
}
